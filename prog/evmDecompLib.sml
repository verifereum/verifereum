(* ------------------------------------------------------------------------
   evmDecompLib: certified block summaries of EVM runtime code.

   Given a contract's runtime code, summarize_code produces one theorem per
   basic block and exit, each a SPEC EVM_MODEL triple over the real semantics
   composed from the per-instruction rules of vfmProgTheory. Nothing here is
   trusted: every summary is proved by SPEC_REFL, SPEC_FRAME, SPEC_COMPOSE and
   SPEC_MOVE_COND from those rules (compose_region also uses SPEC_ADD_CODE,
   SPEC_SUBSET_CODE and case analysis), so a wrong hint or a bug in the composer
   gives a failed summary, never a wrong theorem. What a bug can give is a
   vacuous one, whose precondition no state satisfies; compose refuses the
   two ways known to produce that (see compose).

   Blocks. A block starts at pc 0, at a JUMPDEST, after a JUMPI, at and
   after a CALL-class instruction, or at a pc in config.hints. It runs to
   its terminator (JUMP, JUMPI, STOP, RETURN, REVERT, INVALID, SELFDESTRUCT,
   CALL, CALLCODE, DELEGATECALL, STATICCALL, CREATE, CREATE2), or up to the
   next block start, whichever comes first. A terminator with several rules
   gives one summary per rule: JUMPI gives "take" and "skip". A CALL-class
   instruction is a block of its own because its rule hides every other
   parsed pc, which the code of a longer block would also claim. With
   config.strip_metadata, the compiler's CBOR metadata at the end of the
   code is not searched for blocks (metadata_start).

   Summary format. For a block at pc n with d stack slots read and k left:

     SPEC EVM_MODEL
       (evm_Stack (s0::...::s(d-1)::rest) * evm_PC n * <other resources> *
        cond C * cond G)
       {(n,i0); ...}
       (evm_Stack (e0::...::e(k-1)::rest) * evm_PC x * <resources'>)

   - rest is never inspected: d is the depth the block reads (checked by the
     proof, which fails to reach this shape if d is too small).
   - each e_i, and every resource in the post, is a term over the s_i and
     the entry resources (p.caller, the memory m, the rollback state rb, ...)
     and the memory abbreviations mem<n> defined in C: no intermediate stack
     survives.
   - C is the condition the block needs to run: stack-depth bound, ISL e,
     j = NONE, p.code/p.parsed equal to the contract's code (when a jump or a
     code-reading instruction needs it), JUMPI conditions, static-context
     facts, access-list facts.
   - G is the gas layer: every conjunct that mentions p.gasLimit, other
     than a memory definition (a GAS result written to memory). The
     chain of per-instruction bounds g + c_i <= p.gasLimit is collapsed into
     the strongest one. G cannot be dropped from the precondition (the block
     does need the gas); drop_gas instead hides the gas used in the post, so
     that summaries can be read without the gas arithmetic.

   Next to each theorem, summarize_block returns a block_summary record:
   entry pc, exit kind and target, d, k, entry and exit stack terms, C, G,
   and the ordered list of effects (one per instruction and resource it
   changes, other than the stack, pc, gas used and jump-dest). The record
   is not checked: the effects are read off the per-step theorems, before
   the final simplification, so they may differ in form from the post.

   Memory. A memory term that is not small is abbreviated after each
   instruction as a fresh variable mem<n> with a conjunct mem<n> = t in C,
   so that summaries stay linear in the block's length (abbreviate_memory);
   inline_memory undoes it. A buffer variable named mem... is taken for an
   abbreviation, so rules added with set_rules/add_rules should not use
   such names.

   Simplification. After each instruction the new stack values, effects and
   conditions are simplified with srw_ss, a few list/word lemmas and
   config.simps. Values too large to simplify cheaply (memory, hashes of
   memory) are kept abstract during the step and substituted after it; a
   final pass simplifies them in place. Gas sums are normalised and
   compared on their arithmetic skeleton, with the large summands replaced
   by variables. config.simps run at every step: conditional rewrites over
   memory buffers are slow there, so lemmas needed only on one path are
   better given to the config passed to compose_blocks.

   Rules come from a table keyed by opcode constructor name (rules_for,
   set_rules, add_rules), defaulting to vfmProgTheory's SPEC_<name>. A rule
   is instantiated by matching its code (or its evm_Parsed assertion) against
   the instruction, so parameterised rules (Push n bs, Dup n, Swap n, Log n,
   inst-generic Return/Revert) need no special handling.
   ------------------------------------------------------------------------ *)
structure evmDecompLib :> evmDecompLib =
struct

open HolKernel boolLib bossLib Parse;
open pred_setTheory progTheory set_sepTheory helperLib vfmProgTheory;

val ERR = mk_HOL_ERR "evmDecompLib";

type config = {code_eq : thm, parsed_eq : thm, hints : int list,
               simps : thm list, strip_metadata : bool}

fun default_config code_eq parsed_eq : config =
  {code_eq = code_eq, parsed_eq = parsed_eq, hints = [], simps = [],
   strip_metadata = true}

datatype exit =
    Jump of term
  | JumpITaken of term
  | JumpISkip of int
  | FallThrough of int
  | Halt of string
  | Call of string

type effect = {pc : int, inst : term, resource : string, value : term}

type block_summary =
  {entry : int, variant : string, exit : exit,
   depth : int, height : int,
   entry_stack : term list, exit_stack : term list,
   effects : effect list, cond : term list, gas : term list,
   code : (int * term) list}

type failure = {entry : int, variant : string, pc : int, inst : term,
                reason : string}

datatype outcome = Summary of block_summary * thm
                 | Infeasible of {entry : int, variant : string, cond : term}
                 | Failed of failure

exception Stuck of int * term * string
exception Infeasible_cond of term

(* ------------------------------------------------------------------------
   Instructions and blocks
   ------------------------------------------------------------------------ *)

fun opname inst = fst (dest_const (fst (strip_comb inst)))

(* Metadata. solc appends a CBOR map and its length (2 bytes, big-endian,
   not counting themselves) to the runtime code; Vyper since 0.3.10 appends
   a CBOR array and a length that counts the two bytes, to the init code
   only. Its bytes parse as instructions, so blocks found there would
   describe data. cbor_end returns the index just past the CBOR item at i,
   for definite lengths only, and NONE if it runs past the end. *)
fun cbor_end (bs : int vector) i =
  let
    val n = Vector.length bs
    fun byte j = if j < n then SOME (Vector.sub (bs, j)) else NONE
    fun arg j k = (* the k-byte big-endian argument at j *)
      if j + k > n then NONE
      else SOME (List.foldl (fn (b, a) => a * 256 + b) 0
                   (List.tabulate (k, fn x => Vector.sub (bs, j + x))))
    fun items j 0 = SOME j
      | items j m = case cbor_end bs j of
                      SOME j' => items j' (m - 1) | NONE => NONE
  in
    case byte i of
      NONE => NONE
    | SOME b =>
      let
        val major = b div 32 and info = b mod 32
        val (len, start) =
          if info < 24 then (SOME info, i + 1)
          else if info <= 27 then
            let val k = List.nth ([1, 2, 4, 8], info - 24)
            in (arg (i + 1) k, i + 1 + k) end
          else (NONE, i + 1)
      in
        case (major, len) of
          (_, NONE) => NONE
        | (0, _) => SOME start
        | (1, _) => SOME start
        | (2, SOME l) => if start + l <= n then SOME (start + l) else NONE
        | (3, SOME l) => if start + l <= n then SOME (start + l) else NONE
        | (4, SOME l) => if l <= n then items start l else NONE
        | (5, SOME l) => if 2 * l <= n then items start (2 * l) else NONE
        | (6, SOME _) => cbor_end bs start
        | (7, _) => SOME start
        | _ => NONE
      end
  end

fun code_bytes (cfg : config) =
  #code_eq cfg |> concl |> rhs |> listSyntax.dest_list |> fst
  |> map wordsSyntax.uint_of_word |> Vector.fromList

fun metadata_start cfg =
  let
    val bs = code_bytes cfg
    val n = Vector.length bs
    (* a non-empty map or array, ending at the length bytes *)
    fun ok start header =
      start >= 0 andalso start < n - 2 andalso
      let val b = Vector.sub (bs, start) in
        header (b div 32) andalso b mod 32 <> 0 andalso
        cbor_end bs start = SOME (n - 2)
      end
  in
    if n < 3 then NONE else
    let val l = 256 * Vector.sub (bs, n - 2) + Vector.sub (bs, n - 1) in
      if ok (n - 2 - l) (fn m => m = 5) then SOME (n - 2 - l)
      else if ok (n - l) (fn m => m = 4 orelse m = 5) then SOME (n - l)
      else NONE
    end
  end

(* the instructions before the metadata, when it is stripped *)
fun instructions (cfg : config) =
  let
    val keep = case (#strip_metadata cfg, metadata_start cfg) of
                 (true, SOME m) => (fn n => n < m)
               | _ => K true
  in
    #parsed_eq cfg |> concl |> rhs
    |> find_terms finite_mapSyntax.is_fupdate
    |> map (fn tm => pairSyntax.dest_pair (rand tm))
    |> map (fn (n, tm) => (numSyntax.int_of_term n, tm))
    |> filter (keep o fst)
    |> Listsort.sort (fn ((n, _), (m, _)) => Int.compare (n, m))
  end

fun inst_length inst =
  if opname inst = "Push" then
    1 + length (fst (listSyntax.dest_list (rand inst)))
  else 1

val call_class =
  ["Call", "CallCode", "DelegateCall", "StaticCall", "Create", "Create2"]
val terminators =
  ["Jump", "JumpI", "Stop", "Return", "Revert", "Invalid", "SelfDestruct"]
  @ call_class

fun block_starts cfg =
  let
    val insts = instructions cfg
    val pcs = map fst insts
    fun starts_of (pc, inst) =
      if opname inst = "JumpI" then [pc + inst_length inst]
      else if mem (opname inst) call_class then [pc, pc + inst_length inst]
      else []
    val jumpdests = map fst (filter (fn (_, i) => opname i = "JumpDest") insts)
    val all = 0 :: jumpdests @ List.concat (map starts_of insts)
              @ #hints cfg
  in
    Listsort.sort Int.compare (mk_set (filter (fn n => mem n pcs) all))
  end

fun inst_table cfg = Redblackmap.fromList Int.compare (instructions cfg)

fun block_insts tbl starts start =
  let
    fun go pc acc =
      case Redblackmap.peek (tbl, pc) of
        NONE => rev acc
      | SOME inst =>
          let val acc = (pc, inst) :: acc
              val next = pc + inst_length inst
          in
            if mem (opname inst) terminators orelse mem next starts
            then rev acc else go next acc
          end
  in go start [] end

fun block_instructions cfg = block_insts (inst_table cfg)

(* Stack slots an instruction reads and writes, used only to guess the
   entry depth d; a wrong guess makes the summary fail to reach the
   canonical shape and is retried with d + 1. *)
fun stack_effect inst =
  let
    val name = opname inst
    fun arg () = numSyntax.int_of_term (rand inst)
    fun is l = mem name l
  in
    if name = "Dup" then (arg () + 1, arg () + 2)
    else if name = "Swap" then (arg () + 2, arg () + 2)
    else if name = "Log" then (arg () + 2, 0)
    else if is ["AddMod", "MulMod"] then (3, 1)
    else if is ["Add", "Mul", "Sub", "Div", "SDiv", "Mod", "SMod", "Exp",
                "SignExtend", "LT", "GT", "SLT", "SGT", "Eq", "And", "Or",
                "XOr", "Byte", "ShL", "ShR", "SAR", "Keccak256"] then (2, 1)
    else if is ["IsZero", "Not", "CLZ", "Balance", "CallDataLoad",
                "ExtCodeSize", "ExtCodeHash", "BlockHash", "MLoad", "SLoad",
                "TLoad", "BlobHash"] then (1, 1)
    else if is ["Pop", "Jump", "SelfDestruct"] then (1, 0)
    else if is ["MStore", "MStore8", "SStore", "TStore", "JumpI", "Return",
                "Revert"] then (2, 0)
    else if is ["CallDataCopy", "CodeCopy", "ReturnDataCopy", "MCopy"]
      then (3, 0)
    else if name = "ExtCodeCopy" then (4, 0)
    else if name = "Create" then (3, 1)
    else if name = "Create2" then (4, 1)
    else if is ["Call", "CallCode"] then (7, 1)
    else if is ["DelegateCall", "StaticCall"] then (6, 1)
    else if is ["Stop", "JumpDest", "Invalid"] then (0, 0)
    else (0, 1)
  end

fun depth_guess insts =
  let
    fun go [] (d, h) = d
      | go ((_, i) :: is) (d, h) =
          let val (r, w) = stack_effect i
          in go is (Int.max (d, r - h), h - r + w) end
  in go insts (0, 0) end

(* ------------------------------------------------------------------------
   Rule table
   ------------------------------------------------------------------------ *)

val rule_table : (string, (string * thm) list) Redblackmap.dict ref =
  ref (Redblackmap.mkDict String.compare)

fun set_rules name rules =
  rule_table := Redblackmap.insert (!rule_table, name, rules)

fun default_rules name =
  [(name, DB.fetch "vfmProg" ("SPEC_" ^ name))] handle HOL_ERR _ => []

fun add_rules name rules =
  let val old = case Redblackmap.peek (!rule_table, name) of
                  SOME rs => rs | NONE => default_rules name
  in set_rules name (old @ rules) end

fun rules_for inst =
  let val name = opname inst in
    case Redblackmap.peek (!rule_table, name) of
      SOME rs => rs
    | NONE => default_rules name
  end

val () = set_rules "JumpI" [("take", SPEC_JumpI_take),
                            ("skip", SPEC_JumpI_skip)]
val () = set_rules "Stop" [("outermost", SPEC_Stop_outermost)]
val () = set_rules "Return" [("outermost", SPEC_Return_outermost)]
val () = set_rules "Revert" [("outermost", SPEC_Return_outermost)]
val () = set_rules "Invalid" [("outermost", SPEC_Invalid_outermost)]
val () = set_rules "SelfDestruct" [("outermost", SPEC_SelfDestruct_outermost)]
val () = app (fn n => set_rules n [("call", SPEC_Call)])
             ["Call", "CallCode", "DelegateCall", "StaticCall"]
(* the successful creation, entering the init code; SPEC_Create_fail and
   SPEC_Create_fail_created, which continue in the caller, are not used *)
val () = app (fn n => set_rules n [("create", SPEC_Create)])
             ["Create", "Create2"]

(* ------------------------------------------------------------------------
   Term helpers
   ------------------------------------------------------------------------ *)

val EVM_MODEL_tm = “EVM_MODEL”
val assertion_ty = “:evm_el set set”
val bytes32_ty = “:bytes32”
val cond_tm = “cond : bool -> evm_el set set”

fun spec_parts th = dest_spec (concl th)
fun pre_of th = #2 (spec_parts th)
fun code_of th = #3 (spec_parts th)
fun post_of th = #4 (spec_parts th)
fun stars tm = list_dest dest_star tm
fun head a = fst (strip_comb a)
fun head_name a = fst (dest_const (head a)) handle HOL_ERR _ => "?"
fun is_cond a = same_const (head a) cond_tm handle HOL_ERR _ => false

fun find_part h parts = List.find (fn a => aconv (head a) h) parts

fun post_value name th =
  case List.find (fn a => head_name a = name) (stars (post_of th)) of
    SOME a => SOME (rand a)
  | NONE => NONE

fun thm_frees th =
  HOLset.listItems (FVL (concl th :: hyp th) empty_tmset)

fun rename_apart avoid th =
  let
    fun step (v, (avoid, s)) =
      let val v' = variant avoid v
      in (v' :: avoid, if aconv v v' then s else (v |-> v') :: s) end
    val (_, s) = foldl step (avoid, []) (free_vars (concl th))
  in INST s th end

(* ------------------------------------------------------------------------
   Simplification
   ------------------------------------------------------------------------ *)

(* proved on first use: a theory script loads this library in its header,
   before there is a current theory to prove in *)
val b2w_cache = ref (NONE : thm option)
fun b2w_lemma () =
  case !b2w_cache of
    SOME th => th
  | NONE =>
      let val th = prove(
            “(b2w b = (0w : bytes32) <=> ~b) /\ (b2w b = (1w : bytes32) <=> b)”,
            Cases_on `b` \\ EVAL_TAC)
      in b2w_cache := SOME th; th end

(* memoised: the same constant words recur in every block *)
val word_of_bytes_conv =
  let
    val conv =
      REWR_CONV (SRULE [FUN_EQ_THM] (GSYM byteTheory.word_of_bytes_le_def))
      THENC cv_transLib.cv_eval
    val cache = ref (Redblackmap.mkDict Term.compare)
  in
    fn tm =>
      case Redblackmap.peek (!cache, tm) of
        SOME th => th
      | NONE =>
          let val th = conv tm
          in cache := Redblackmap.insert (!cache, tm, th); th end
  end

val word_of_bytes_ss = simpLib.conv_ss
  {name = "word_of_bytes_ss", trace = 3,
   key = SOME ([], “word_of_bytes F (0w : 'a word) (l : word8 list)”),
   conv = K (K (fn tm =>
     if List.null (free_vars tm) then word_of_bytes_conv tm
     else raise ERR "word_of_bytes_ss" "not ground"))}

val stack_bound_lemma =
  CONJ (DECIDE “n <= m ==> n <= x + m:num”) (DECIDE “n < m ==> n < x + m:num”);

fun base_simps () =
  [listTheory.EL_restricted, listTheory.EL_simp_restricted,
   listTheory.DROP_compute, arithmeticTheory.ADD1,
   GSYM arithmeticTheory.ADD_ASSOC, stack_bound_lemma, b2w_lemma (),
   vfmOperationTheory.opcode_def, wordsTheory.w2n_n2w,
   vfmConstantsTheory.log_topic_cost_def,
   vfmConstantsTheory.log_data_cost_def]

(* Facts about the contract's code. A condition or value mentioning p.code or
   p.parsed is rewritten under the assumption that they are the contract's
   code and parsed code; that assumption becomes a condition of the block.
   insts is the instructions by pc and simp the simplifier, built once
   since building a simpset is a large part of each call's cost. *)
type code_facts =
  {code_c : term, parsed_c : term, length_th : thm,
   flookup : term -> thm, insts : (int, term) Redblackmap.dict, simp : conv}

fun mk_code_facts (cfg : config) =
  let
    val code_c = lhs (concl (#code_eq cfg))
    val parsed_c = lhs (concl (#parsed_eq cfg))
    val length_th =
      (RAND_CONV (REWR_CONV (#code_eq cfg)) THENC EVAL)
        (listSyntax.mk_length code_c)
    val cache = ref (Redblackmap.mkDict Int.compare)
    fun flookup n_tm =
      let val n = numSyntax.int_of_term n_tm in
        case Redblackmap.peek (!cache, n) of
          SOME th => th
        | NONE =>
            let val th = (RATOR_CONV (RAND_CONV (REWR_CONV (#parsed_eq cfg)))
                          THENC EVAL)
                           (finite_mapSyntax.mk_flookup (parsed_c, n_tm))
            in cache := Redblackmap.insert (!cache, n, th); th end
      end
  in
    {code_c = code_c, parsed_c = parsed_c, length_th = length_th,
     flookup = flookup, insts = inst_table cfg,
     simp = SIMP_CONV (srw_ss() ++ word_of_bytes_ss ++
                       simpLib.rewrites (base_simps () @ #simps cfg)) []}
  end

val code_pat = “(p : message_parameters).code”
val parsed_pat = “(p : message_parameters).parsed”

fun code_assumptions (cf : code_facts) tm =
  let
    fun accessed pat = find_terms (fn t => can (match_term pat) t
                                           andalso is_var (rand t)) tm
    val codes = map (fn t => ASSUME (mk_eq (t, #code_c cf))) (accessed code_pat)
    val parseds = map (fn t => ASSUME (mk_eq (t, #parsed_c cf)))
                      (accessed parsed_pat)
  in codes @ parseds end

fun flookup_conv (cf : code_facts) tm =
  let val (m, n) = finite_mapSyntax.dest_flookup tm in
    if aconv m (#parsed_c cf) andalso numSyntax.is_numeral n
    then #flookup cf n else raise ERR "flookup_conv" ""
  end

(* simplify a term, using the code facts when it mentions p.code/p.parsed *)
fun simp_term (cf : code_facts) tm =
  let
    val assums = code_assumptions cf tm
    val c1 = (if List.null assums then ALL_CONV
              else PURE_REWRITE_CONV assums
                   THENC PURE_REWRITE_CONV [#length_th cf])
             THENC DEPTH_CONV (flookup_conv cf)
  in QCONV (c1 THENC #simp cf) tm end

(* ------------------------------------------------------------------------
   Conditions as hypotheses
   ------------------------------------------------------------------------ *)

(* move the precondition's cond into the hypotheses, one per conjunct *)
fun undisch_cond th =
  let val pre = pre_of th in
    if is_cond (snd (dest_star pre) handle HOL_ERR _ => pre) andalso
       can dest_star pre
    then
      let
        val th1 = UNDISCH (CONV_RULE (REWR_CONV SPEC_MOVE_COND) th)
        val c = rand (snd (dest_star pre))
      in PROVE_HYP (LIST_CONJ (map ASSUME (strip_conj c))) th1 end
    else th
  end

fun undisch_conds th =
  let val th' = undisch_cond th
  in if concl th' ~~ concl th then th else undisch_conds th' end

(* simplify hypothesis c of th; T is discharged, F raises *)
fun simp_hyp cfg cf c th =
  let
    val eq = simp_term cf c
    val c' = rhs (concl eq)
  in
    if aconv c' T then PROVE_HYP (EQT_ELIM eq) th
    else if aconv c' F then raise Infeasible_cond c
    else if aconv c c' then th
    else
      let val cs = strip_conj c'
          val c'_th = LIST_CONJ (map ASSUME cs)
      in PROVE_HYP (EQ_MP (SYM eq) c'_th) th end
  end

fun simp_hyps cfg cf hs th = foldl (fn (c, th) => simp_hyp cfg cf c th) th hs

(* Memory abbreviations: a variable mem<n> of type buffer, defined by a
   hypothesis mem<n> = t (see abbreviate_memory) *)
val buffer_ty = “:buffer”
fun is_mem_abbrev v =
  is_var v andalso type_of v = buffer_ty andalso
  String.isPrefix "mem" (fst (dest_var v))
fun is_mem_def c =
  is_eq c andalso is_mem_abbrev (lhs c)
fun mem_def_of c = if is_mem_def c then SOME (dest_eq c) else NONE

(* a hypothesis v = t (or (v1,...,vn) = t) defining variables local to one
   rule: they are instantiated away. A memory abbreviation is not local:
   instantiating it would undo abbreviate_memory. *)
fun local_def fixed c =
  let
    val (l, r) = dest_eq c
    fun local_var v = is_var v andalso not (tmem v fixed) andalso
                      not (is_mem_abbrev v)
    fun def_of (l, r) =
      if local_var l andalso not (free_in l r) then SOME [(l, r)]
      else if pairSyntax.is_pair l then
        let val vs = pairSyntax.strip_pair l in
          if List.all local_var vs andalso
             List.all (fn v => not (free_in v r)) vs andalso
             length (op_mk_set aconv vs) = length vs
          then
            let
              fun split [v] t = [(v, t)]
                | split (v :: vs) t =
                    (v, pairSyntax.mk_fst t) :: split vs (pairSyntax.mk_snd t)
                | split [] _ = []
            in SOME (split vs r) end
          else NONE
        end
      else NONE
  in
    case def_of (l, r) of SOME d => SOME d | NONE => def_of (r, l)
  end handle HOL_ERR _ => NONE

fun eliminate_locals cfg cf fixed th =
  let
    val hs = hyp th
    val defs = List.mapPartial (local_def fixed) hs
    val defined = map fst (List.concat defs)
    fun independent d =
      List.all (fn (_, r) => not (List.exists (fn v => free_in v r) defined)) d
  in
    case (List.find independent defs, defs) of
      (_, []) => th
    | (found, d0 :: _) =>
        let
          val d = case found of SOME d => d | NONE => d0
          val th1 = INST (map (fn (v, t) => v |-> t) d) th
          val new = filter (fn h => not (tmem h hs)) (hyp th1)
        in eliminate_locals cfg cf fixed (simp_hyps cfg cf new th1) end
  end

(* ------------------------------------------------------------------------
   Instantiating and composing rules
   ------------------------------------------------------------------------ *)

val parsed_tm = “evm_Parsed”

(* instantiate the rule at (pc, inst) by matching its code or its
   evm_Parsed assertion *)
fun inst_at (pc, inst) rule =
  let
    val pc_tm = numSyntax.term_of_int pc
    val target = pairSyntax.mk_pair (pc_tm, inst)
    val code = code_of rule
    val pat =
      if pred_setSyntax.is_insert code then
        fst (pred_setSyntax.dest_insert code)
      else
        case find_part parsed_tm (stars (pre_of rule)) of
          SOME a => let val (f, i) = dest_comb a
                    in pairSyntax.mk_pair (rand f, i) end
        | NONE => raise ERR "inst_at" "rule without code"
  in INST_TY_TERM (match_term pat target) rule end

(* a stack term x0::...::x(n-1)::r as ([x0, ..., x(n-1)], r) *)
fun strip_stack tm =
  if listSyntax.is_cons tm then
    let val (h, t) = listSyntax.dest_cons tm
        val (hs, r) = strip_stack t
    in (h :: hs, r) end
  else ([], tm)

(* the substitution instantiating the rule's precondition from the current
   post *)
fun match_pre fixed post_parts rule =
  let
    val fixed_set = HOLset.addList (empty_tmset, fixed)
    fun go [] theta = theta
      | go (a :: rest) theta =
          case find_part (head a) post_parts of
            NONE => go rest theta
          | SOME q =>
              let val (s, _) = match_terml [] fixed_set (subst theta a) q
              in go rest (theta @ s) end
  in go (filter (not o is_cond) (stars (pre_of rule))) [] end

(* Values from the current post that are large (memory, accounts, hashes
   of memory, ...) are kept abstract while the rule is simplified and
   substituted afterwards, so each step simplifies small terms only; small
   values (literals, stack slots, short sums) are substituted at once so
   that constants fold. A stack is split into its elements. *)
val abstract_limit = 40

fun small t =
  let
    fun size t n =
      if n > abstract_limit then n
      else if is_comb t then
        let val (f, x) = dest_comb t in size x (size f (n + 1)) end
      else if is_abs t then size (snd (dest_abs t)) (n + 1)
      else n + 1
  in size t 0 <= abstract_limit end

fun abstract theta =
  let
    fun one ({redex = v, residue = t}, (now, later)) =
      if small t then ((v |-> t) :: now, later)
      else if listSyntax.is_cons t then
        let
          val (es, tl) = strip_stack t
          fun elt (e, (es', later)) =
            if small e then (e :: es', later)
            else let val a = genvar (type_of e)
                 in (a :: es', (a |-> e) :: later) end
          val (es', later) = foldr elt ([], later) es
        in ((v |-> foldr listSyntax.mk_cons tl es') :: now, later) end
      else (now, (v |-> t) :: later)
  in foldl one ([], []) theta end

(* Permuting star products. Every resource appears at most once in a pre
   or post, so a product is put in a canonical order by head name with
   STAR_ASSOC and STAR_COMM steps that never compare the (large) arguments. *)
fun is_star tm = can dest_star tm

fun flat_star tm =
  if not (is_star tm) then ALL_CONV tm
  else
    let val th = QCONV (LAND_CONV flat_star THENC RAND_CONV flat_star) tm
        val r = rand (rhs (concl th))
    in
      if is_star r then
        CONV_RULE (RAND_CONV (REWR_CONV STAR_ASSOC THENC LAND_CONV flat_star))
                  th
      else th
    end

(* a left-nested product = x * rest, x the part with head name key *)
fun pull_star key tm =
  let val (l, a) = dest_star tm in
    if head_name a = key then REWR_CONV STAR_COMM tm
    else if not (is_star l) then
      (if head_name l = key then ALL_CONV tm
       else raise ERR "pull_star" key)
    else (LAND_CONV (pull_star key) THENC REWR_CONV (GSYM STAR_ASSOC)) tm
  end

fun canon_star [] tm = ALL_CONV tm
  | canon_star [_] tm = ALL_CONV tm
  | canon_star (k :: ks) tm =
      (pull_star k THENC RAND_CONV (canon_star ks)) tm

fun star_eq tm1 tm2 =
  let
    val keys = Listsort.sort String.compare (map head_name (stars tm1))
    val unique = length (mk_set keys) = length keys
  in
    if unique then
      TRANS (QCONV (flat_star THENC canon_star keys) tm1)
            (SYM (QCONV (flat_star THENC canon_star keys) tm2))
    else
      EQT_ELIM (SIMP_CONV bool_ss [AC STAR_ASSOC STAR_COMM] (mk_eq (tm1, tm2)))
  end

(* the resource a part asserts: f for f x and for ~f *)
fun resource a =
  if same_const (head a) “SEP_HIDE” then rand a else head a
  handle HOL_ERR _ => head a

(* SPEC x P C1 Q and SPEC x R C2 S with Q and R agreeing on shared
   resources: frame each with what the other has, compose. Two framings
   would give a precondition no state satisfies, and are refused: framing
   onto th a resource that only its post hides (after drop_gas), and
   framing a rule that hides parsed pcs (a CALL-class rule) onto code,
   whose pcs that rule's evm_hide_Parsed would claim a second time. *)
fun frame th [] = th
  | frame th xs = SPEC (list_mk_star xs assertion_ty) (MATCH_MP SPEC_FRAME th)

fun compose th r =
  let
    val qs = stars (post_of th)
    val rs = stars (pre_of r)
    fun missing xs ys =
      filter (fn y => not (List.exists (fn x => aconv (resource x) (resource y))
                             xs)) ys
    val add_th = missing qs rs
    val add_r = missing rs qs
    fun hidden a = same_const (head a) “SEP_HIDE” handle HOL_ERR _ => false
    val _ = case List.find (fn q => hidden q andalso
                              List.exists (fn a => aconv (resource a)
                                                         (resource q)) rs) qs of
              SOME q => raise ERR "compose"
                          (term_to_string q ^ " is hidden but read next")
            | NONE => ()
    val _ = if List.exists (fn a => head_name a = "evm_hide_Parsed") add_th
               andalso not (pred_setSyntax.is_empty (code_of th))
            then raise ERR "compose"
                   "a rule hiding parsed pcs cannot follow other instructions"
            else ()
    val th1 = frame th add_th
    val r1 = frame r add_r
    val eq = star_eq (post_of th1) (pre_of r1)
    val th2 = CONV_RULE (RAND_CONV (K eq)) th1
  in
    MATCH_MP SPEC_COMPOSE (CONJ th2 r1)
  end

(* ------------------------------------------------------------------------
   Summarizing a block
   ------------------------------------------------------------------------ *)

val stack_tm = “evm_Stack”
val pc_tm = “evm_PC”
val gas_tm = “evm_GasUsed”
val gaslimit_pat = “(p : message_parameters).gasLimit”
val untracked = ["evm_Stack", "evm_PC", "evm_GasUsed", "evm_JumpDest"]

fun entry_stack d =
  let val ss = List.tabulate (d, fn i =>
                 mk_var ("s" ^ Int.toString i, bytes32_ty))
      val rest = mk_var ("rest", listSyntax.mk_list_type bytes32_ty)
  in (ss, rest, foldr listSyntax.mk_cons rest ss) end

fun initial_th entry stack =
  let
    val pre = list_mk_star [mk_comb (stack_tm, stack),
                            mk_comb (pc_tm, numSyntax.term_of_int entry)]
                           assertion_ty
    val empty = pred_setSyntax.mk_empty
                  (pred_setSyntax.dest_set_type (type_of (code_of SPEC_Add)))
  in ISPECL [EVM_MODEL_tm, pre, empty] SPEC_REFL end

(* compose a rule (after prep) onto th: instantiate its precondition from
   th's post, discharge what it can, compose, simplify the post *)
fun apply_rule cfg cf prep rule th =
  let
    val fixed0 = thm_frees th
    val r1 = prep (rename_apart fixed0 rule)
    val (now, later) = abstract (match_pre fixed0 (stars (post_of th)) r1)
    val r2 = INST now r1
    val r3 = undisch_conds r2
    val fixed = fixed0 @ free_vars (pre_of r3)
    val r4 = simp_hyps cfg cf (hyp r3) r3
    val r5 = eliminate_locals cfg cf fixed r4
    val r6 = CONV_RULE (RAND_CONV (simp_term cf)) r5
  in compose th (INST later r6) end

fun mentions_gas t =
  can (find_term (fn x => can (match_term gaslimit_pat) x)) t

(* a conjunct of G: a memory definition stays in C even when its memory
   mentions p.gasLimit (a GAS result written to memory) *)
fun is_gas_cond c = mentions_gas c andalso not (is_mem_def c)

(* The linear-arithmetic skeleton of a term: its maximal non-arithmetic
   subterms (memory costs, storage lookups, p.gasLimit, ...) replaced by
   variables. Gas bounds are sums of large terms; arithmetic decision and
   normalisation on the skeleton are fast where on the term they are not. *)
fun arith_skeleton tm =
  let
    val tbl = ref ([] : (term * term) list)
    fun atom t =
      case List.find (fn (u, _) => aconv u t) (!tbl) of
        SOME (_, v) => v
      | NONE => let val v = genvar (type_of t)
                in tbl := (t, v) :: !tbl; v end
    fun arith t =
      numSyntax.is_plus t orelse numSyntax.is_minus t orelse
      numSyntax.is_mult t orelse numSyntax.is_less t orelse
      numSyntax.is_leq t orelse is_imp_only t orelse is_conj t orelse
      is_neg t
    fun go t =
      if numSyntax.is_numeral t then t
      else if arith t then
        let val (f, args) = strip_comb t in list_mk_comb (f, map go args) end
      else atom t
    val skel = go tm
  in (skel, map (fn (t, v) => v |-> t) (!tbl)) end

fun skeleton_conv c tm =
  let val (skel, theta) = arith_skeleton tm in INST theta (c skel) end

val arith_norm = skeleton_conv (QCONV (SIMP_CONV arith_ss []))
val arith_decide = skeleton_conv DECIDE

(* The final simplification of a block: the large terms the steps kept
   abstract are simplified in place, and the gas bounds and gas used are
   normalised (constants summed) *)
fun polish cfg cf th =
  let
    val th1 = simp_hyps cfg cf (hyp th) th
    val th2 = CONV_RULE (RAND_CONV (simp_term cf)) th1
    fun norm_hyp (h, th) =
      let val eq = arith_norm h in
        if aconv (rhs (concl eq)) h then th
        else PROVE_HYP (EQ_MP (SYM eq) (ASSUME (rhs (concl eq)))) th
      end
    val th3 = foldl norm_hyp th2 (filter mentions_gas (hyp th2))
    fun gas_used a =
      if head_name a = "evm_GasUsed" then RAND_CONV arith_norm a
      else NO_CONV a
  in
    CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV gas_used)) th3
  end

(* Memory is abbreviated. A memory read (MLOAD, KECCAK256, a copy's source)
   puts the whole memory term into a stack value, and that value can be an
   offset or size of the next write, whose memory term then holds the
   previous one several times over: the terms grow exponentially in the
   number of writes. So when a step leaves a memory term that is not small,
   it is replaced by a fresh variable mem<n> and the equation mem<n> = t
   becomes a hypothesis, and so a conjunct of C. Each definition then
   mentions the previous memory as one variable, and the summary stays
   linear in the block's length. The theorem holds for every mem<n>, so a
   consumer gets the memory back by instantiating mem<n> to its definition,
   which discharges the conjunct. *)
fun abbreviate_memory th =
  case post_value "evm_Memory" th of
    NONE => th
  | SOME t =>
      if small t then th
      else
        let
          val frees = thm_frees th
          val n = length (filter is_mem_abbrev frees) + 1
          val v = variant frees (mk_var ("mem" ^ Int.toString n, buffer_ty))
          val eq = SYM (ASSUME (mk_eq (v, t)))
          fun conv a =
            if head_name a = "evm_Memory" andalso aconv (rand a) t
            then RAND_CONV (K eq) a else NO_CONV a
        in CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV conv)) th end

fun step cfg cf (pc, inst) (label, rule) th =
  apply_rule cfg cf (inst_at (pc, inst)) rule th
  handle Infeasible_cond c => raise Infeasible_cond c
       | HOL_ERR e =>
           raise Stuck (pc, inst, label ^ ": " ^ top_function_of e ^ ": " ^
                                  message_of e)

fun effects_of_step (pc, inst) th0 th1 =
  let
    val bs0 = stars (post_of th0)
    fun absent a = not (List.exists (fn b => aconv (head a) (head b)) bs0)
    val bs = bs0 @ filter absent (stars (pre_of th1))
    fun changed a =
      not (mem (head_name a) untracked) andalso
      (case find_part (head a) bs of
         SOME b => not (aconv b a)
       | NONE => true)
  in
    map (fn a => {pc = pc, inst = inst, resource = head_name a,
                  value = rand a})
        (filter changed (stars (post_of th1)))
  end

fun find_max imp [] = NONE
  | find_max imp (t :: ts) =
      SOME (foldl (fn (t, m) => if can imp (t, m) then m else t) t ts)

(* For bounds f (k + xs) r, with k a numeral and xs the other summands:
   one with a smaller k does not in general imply one with a larger k and
   the same f, xs and r, so collapse does not try to prove it. The failing
   arith_decide calls this saves were most of collapse's cost. A case
   where it would follow anyway (say, from facts about xs and r) only
   leaves both bounds in the summary. *)
fun bound_parts t =
  let
    fun summands t =
      if numSyntax.is_plus t then
        let val (a, b) = numSyntax.dest_plus t in summands a @ summands b end
      else [t]
    val (f, l, r) = case strip_comb t of
                      (f, [l, r]) => (f, l, r)
                    | _ => raise ERR "bound_parts" "not binary"
    val (ns, xs) = partition numSyntax.is_numeral (summands l)
    val k = foldl (fn (n, a) => Arbnum.+ (numSyntax.dest_numeral n, a))
                  Arbnum.zero ns
  in SOME (f, r, Listsort.sort Term.compare xs, k) end
  handle HOL_ERR _ => NONE

fun not_implied (t, m) =
  case (bound_parts t, bound_parts m) of
    (SOME (f1, r1, xs1, k1), SOME (f2, r2, xs2, k2)) =>
      aconv f1 f2 andalso aconv r1 r2 andalso
      ListPair.allEq (uncurry aconv) (xs1, xs2) andalso Arbnum.< (k2, k1)
  | _ => false

(* keep the strongest of a family of bounds, discharging the others *)
fun collapse pred th =
  let
    val hs = filter pred (hyp th)
    fun imp (t, m) =
      if not_implied (t, m) then raise ERR "collapse" "not implied"
      else arith_decide (mk_imp (m, t))
  in
    case find_max imp hs of
      NONE => th
    | SOME m =>
        foldl (fn (t, th) =>
                 if aconv t m then th
                 else (PROVE_HYP (MP (imp (t, m)) (ASSUME m)) th
                       handle HOL_ERR _ => th)) th hs
  end

fun is_gas_bound t =
  numSyntax.is_leq t andalso can (match_term gaslimit_pat) (rand t)
fun is_stack_bound rest t =
  numSyntax.is_less t andalso
  can (find_term (aconv (listSyntax.mk_length rest))) (rator t)

(* discharge the hypotheses cs into a precondition cond *)
fun move_cond cs th =
  if List.null cs then th
  else
    let
      val c = list_mk_conj cs
      val th1 = foldl (fn (cth, th) => PROVE_HYP cth th) th
                      (CONJUNCTS (ASSUME c))
    in CONV_RULE (REWR_CONV (GSYM SPEC_MOVE_COND)) (DISCH c th1) end

val code_norm =
  PURE_REWRITE_CONV [UNION_EMPTY, INSERT_UNION_EQ]

fun dest_code code =
  map (fn t => let val (n, i) = pairSyntax.dest_pair t
               in (numSyntax.int_of_term n, i) end)
      (pred_setSyntax.strip_set code)

fun exit_of label (pc, inst) th =
  let
    val name = opname inst
    val target = case post_value "evm_PC" th of
                   SOME t => t | NONE => raise ERR "exit_of" "no evm_PC"
  in
    if name = "Jump" then Jump target
    else if name = "JumpI" then
      (if label = "skip" then JumpISkip (numSyntax.int_of_term target)
       else JumpITaken target)
    else if mem name call_class then Call label
    else if mem name terminators then Halt label
    else FallThrough (numSyntax.int_of_term target)
  end

(* the hypotheses of th not yet in seen, in a stable order *)
fun hyp_order seen th =
  filter (fn h => not (tmem h seen)) (rev (hyp th))

fun stack_of parts =
  case List.find (fn a => head_name a = "evm_Stack") parts of
    SOME a => strip_stack (rand a)
  | NONE => raise ERR "stack_of" "no evm_Stack"

fun stack_rest th = snd (stack_of (stars (pre_of th)))

(* collapse the bounds and move the hypotheses into cond C * cond G, in the
   order they first appeared (seen) *)
fun close_conds seen th =
  let
    val th1 = th |> collapse is_gas_bound
                 |> collapse (is_stack_bound (stack_rest th))
    val order = filter (fn h => tmem h (hyp th1))
                       (seen @ hyp_order seen th)
    val (gas, cnd) = partition is_gas_cond order
    val th2 = th1 |> move_cond cnd |> move_cond gas
                  |> CONV_RULE (RATOR_CONV (RAND_CONV code_norm)
                                THENC PRE_CONV (PURE_REWRITE_CONV
                                                  [STAR_ASSOC]))
    val _ = if List.null (hyp th2) then ()
            else raise ERR "close_conds" "hypotheses left"
  in (th2, cnd, gas) end

(* the conjuncts of a closed summary's cond C and cond G *)
fun closed_conds th =
  let
    val cs = map rand (filter is_cond (stars (pre_of th)))
    val (gas, cnd) = partition (List.exists is_gas_cond o strip_conj) cs
  in (List.concat (map strip_conj cnd), List.concat (map strip_conj gas)) end

(* Undo abbreviate_memory in a closed summary: each mem<n> is instantiated
   to its definition, which discharges the conjunct defining it. *)
fun inline_memory th =
  let
    val (cnd0, gas0) = closed_conds th
    fun go th cnd gas =
      case List.mapPartial mem_def_of cnd of
        [] => (th, cnd, gas)
      | (v, t) :: _ =>
          let
            val s = [v |-> t]
            val th1 = PROVE_HYP (REFL t) (INST s th)
            val cnd' = filter (not o aconv (mk_eq (t, t))) (map (subst s) cnd)
          in go th1 cnd' (map (subst s) gas) end
    val (th1, cnd, gas) = go (undisch_conds th) cnd0 gas0
    val th2 = th1 |> move_cond cnd |> move_cond gas
                  |> CONV_RULE (PRE_CONV (PURE_REWRITE_CONV [STAR_ASSOC]))
    val _ = if List.null (hyp th2) then ()
            else raise ERR "inline_memory" "hypotheses left"
  in th2 end

(* when r reads deeper than th leaves visible, th's rest becomes
   s(d)::...::rest, extending its entry stack s0::...::s(d-1)::rest *)
fun widen_stack th r =
  let
    val (es, tl) = stack_of (stars (post_of th))
    val (ss, _) = stack_of (stars (pre_of r))
    val n = length ss - length es
  in
    if n <= 0 orelse not (is_var tl) then []
    else
      let
        val d = length (fst (stack_of (stars (pre_of th))))
        fun fresh (i, avoid) =
          variant avoid (mk_var ("s" ^ Int.toString (d + i), bytes32_ty))
        val xs = rev (foldl (fn (i, xs) => fresh (i, xs @ thm_frees th) :: xs)
                            [] (List.tabulate (n, I)))
      in [tl |-> foldr listSyntax.mk_cons tl xs] end
  end

(* Composing renames the summaries' memory abbreviations apart (mem1,
   mem1', ...); this numbers them again, mem1, mem2, ..., in the order they
   are defined, and lists the definitions in that order where seen had
   them. *)
fun renumber_memory seen th =
  let
    val defs = List.mapPartial mem_def_of (hyp th)
    val vs = map fst defs
    fun order placed [] = rev placed
      | order placed rest =
          let
            fun ready (_, t) =
              List.all (fn v => not (free_in v t) orelse
                                tmem v (map fst placed)) vs
          in
            case List.partition ready rest of
              (d :: ds, others) => order (d :: placed) (ds @ others)
            | ([], _) => raise ERR "renumber_memory" "cyclic definitions"
          end
    val sorted = order [] defs
    val s = mapi (fn i => fn (v, _) =>
                    v |-> mk_var ("mem" ^ Int.toString (i + 1), buffer_ty))
                 sorted
    val th1 = INST s th
    val sorted_defs = map (fn (v, t) => subst s (mk_eq (v, t))) sorted
    fun fill [] _ = []
      | fill (c :: cs) ds =
          if isSome (mem_def_of c) then
            (case ds of d :: ds' => d :: fill cs ds' | [] => fill cs [])
          else subst s c :: fill cs ds
    val n = length (List.filter (isSome o mem_def_of) seen)
    val seen1 = fill seen sorted_defs @
                List.drop (sorted_defs, Int.min (n, length sorted_defs))
  in (seen1, th1) end

(* th, with the conditions seen so far, followed by the summary r; a
   failure is raised as caller's, at the place named by at *)
fun compose_step cfg cf caller at (th, seen) r =
  let
    val theta = widen_stack th r
    val seen = map (subst theta) seen
    val th' = apply_rule cfg cf I r (INST theta th)
              handle HOL_ERR e =>
                raise ERR caller (at ^ ": " ^ top_function_of e ^ ": " ^
                                  message_of e)
  in (th', seen @ hyp_order seen th') end

fun compose_blocks cfg [] = raise ERR "compose_blocks" "no summaries"
  | compose_blocks cfg (th :: ths) =
  let
    val cf = mk_code_facts cfg
    val th0 = undisch_conds th
    fun go ((i, r), acc) =
      compose_step cfg cf "compose_blocks" ("summary " ^ Int.toString i) acc r
    val numbered = ListPair.zip (List.tabulate (length ths, fn i => i + 1), ths)
    val (th, seen) = foldl go (th0, hyp_order [] th0) numbered
  in #1 (uncurry close_conds (renumber_memory seen (polish cfg cf th))) end
  handle Infeasible_cond c =>
    raise ERR "compose_blocks" (term_to_string c ^ " is false on this path")

fun summarize_variant cfg cf entry insts d =
  let
    val (ss, rest, stack) = entry_stack d
    val (body, (tpc, tinst)) = (List.take (insts, length insts - 1),
                                List.last insts)
    fun run (pc_inst, (th, effs, seen)) =
      case rules_for (snd pc_inst) of
        [(label, rule)] =>
          let val th' = step cfg cf pc_inst (label, rule) th
              val th'' = abbreviate_memory th'
          in (th'', effs @ effects_of_step pc_inst th th',
              seen @ hyp_order seen th'')
          end
      | [] => raise Stuck (fst pc_inst, snd pc_inst, "no rule")
      | _ => raise Stuck (fst pc_inst, snd pc_inst,
                          "several rules for a non-terminator")
    val (th_body, effs, seen) = foldl run (initial_th entry stack, [], []) body
    val variants = rules_for tinst
    val _ = if List.null variants then raise Stuck (tpc, tinst, "no rule")
            else if length variants > 1 andalso
                    not (mem (opname tinst) terminators)
            then raise Stuck (tpc, tinst, "several rules for a non-terminator")
            else ()
    fun finish (label, rule) =
      let
        val th0 = step cfg cf (tpc, tinst) (label, rule) th_body
        val effs = effs @ effects_of_step (tpc, tinst) th_body th0
        val th0' = abbreviate_memory th0
        val th1 = polish cfg cf th0'
        val (th3, cnd, gas) = close_conds (seen @ hyp_order seen th0') th1
        val is_call = mem (opname tinst) call_class
        val post_stack = case post_value "evm_Stack" th3 of
                           SOME t => t
                         | NONE => raise ERR "summarize" "no evm_Stack"
        val (es, tl) = if is_call then ([], rest) else strip_stack post_stack
        val _ = if aconv tl rest then ()
                else raise Stuck (tpc, tinst, "stack not canonical")
      in
        Summary ({entry = entry,
                  variant = if mem (opname tinst) terminators then label
                            else "",
                  exit = exit_of label (tpc, tinst) th1,
                  depth = d, height = length es,
                  entry_stack = ss, exit_stack = es, effects = effs,
                  cond = cnd, gas = gas, code = dest_code (code_of th3)},
                 th3)
      end
      handle Infeasible_cond c =>
               Infeasible {entry = entry, variant = label, cond = c}
           | Stuck (pc, i, msg) =>
               Failed {entry = entry, variant = label, pc = pc, inst = i,
                       reason = msg}
           | HOL_ERR e =>
               Failed {entry = entry, variant = label, pc = tpc, inst = tinst,
                       reason = top_function_of e ^ ": " ^ message_of e}
  in
    map finish variants
  end
  handle Infeasible_cond c =>
           [Infeasible {entry = entry, variant = "", cond = c}]
       | Stuck (pc, i, msg) =>
           [Failed {entry = entry, variant = "", pc = pc, inst = i,
                    reason = msg}]

fun is_stack_failure (Failed {reason, ...}) = reason = "stack not canonical"
  | is_stack_failure _ = false

fun summarize_with cfg cf starts entry =
  let
    val insts = block_insts (#insts cf) starts entry
    fun try d tries =
      let val res = summarize_variant cfg cf entry insts d in
        if tries > 0 andalso List.exists is_stack_failure res
        then try (d + 1) (tries - 1) else res
      end
  in
    if List.null insts then
      [Failed {entry = entry, variant = "", pc = entry, inst = T,
               reason = "no instruction"}]
    else try (depth_guess insts) 2
  end

fun summarize_block cfg entry =
  summarize_with cfg (mk_code_facts cfg) (block_starts cfg) entry

fun summarize_code cfg =
  let
    val cf = mk_code_facts cfg
    val starts = block_starts cfg
  in List.concat (map (summarize_with cfg cf starts) starts) end

fun summaries outcomes =
  List.mapPartial (fn Summary s => SOME s | _ => NONE) outcomes

fun drop_gas th = HIDE_POST_RULE gas_tm th

(* ------------------------------------------------------------------------
   Printing
   ------------------------------------------------------------------------ *)

fun tm_str t =
  String.translate (fn #"\n" => " " | c => String.str c) (term_to_string t)

fun exit_to_string (Jump t) = "jump " ^ tm_str t
  | exit_to_string (JumpITaken t) = "jumpi taken " ^ tm_str t
  | exit_to_string (JumpISkip n) = "jumpi skip " ^ Int.toString n
  | exit_to_string (FallThrough n) = "fallthrough " ^ Int.toString n
  | exit_to_string (Halt s) = "halt (" ^ s ^ ")"
  | exit_to_string (Call s) = "call (" ^ s ^ ")"

fun block_summary_to_string (s : block_summary) =
  let
    fun lines f xs = String.concat (map (fn x => "    " ^ f x ^ "\n") xs)
  in
    "block " ^ Int.toString (#entry s) ^
    (if #variant s = "" then "" else " [" ^ #variant s ^ "]") ^
    ": " ^ exit_to_string (#exit s) ^
    ", d = " ^ Int.toString (#depth s) ^
    ", k = " ^ Int.toString (#height s) ^
    ", " ^ Int.toString (length (#code s)) ^ " instructions\n" ^
    "  exit stack:\n" ^ lines tm_str (#exit_stack s) ^
    "  effects:\n" ^
    lines (fn {pc, resource, value, ...} =>
             Int.toString pc ^ " " ^ resource ^ " := " ^ tm_str value)
          (#effects s) ^
    "  cond:\n" ^ lines tm_str (#cond s) ^
    "  gas:\n" ^ lines tm_str (#gas s)
  end

fun outcome_to_string (Summary (s, _)) = block_summary_to_string s
  | outcome_to_string (Infeasible {entry, variant, cond}) =
      "block " ^ Int.toString entry ^
      (if variant = "" then "" else " [" ^ variant ^ "]") ^ ": infeasible, " ^
      tm_str cond ^ " is false\n"
  | outcome_to_string (Failed {entry, variant, pc, inst, reason}) =
      "block " ^ Int.toString entry ^
      (if variant = "" then "" else " [" ^ variant ^ "]") ^
      ": FAILED at " ^ Int.toString pc ^ " (" ^ tm_str inst ^ "): " ^
      reason ^ "\n"


(* ------------------------------------------------------------------------
   Composing a region

   compose_region follows every path from a triple's exit, composing at
   each pc every summary that starts there and dropping the ones whose
   conditions are false on the path. Where two survive (a JUMPI's take and
   skip), the path splits; the guard b of the split is the conjunction of
   the conditions only the first side has, and the second side's are
   implied by ~b. Each side is walked on its own, and the two triples

     H1, b  |- SPEC m P c1 Q1        H2, ~b |- SPEC m P c2 Q2

   are merged by cases on b (DISJ_CASES) after weakening each to the code
   c1 UNION c2 and to the postcondition if b then Q1 else Q2. The
   conditions both sides have stay as they are; memory definitions stay
   too (each side's mem<n> are renamed apart first, and a definition of a
   variable the other side never mentions constrains nothing there); the
   rest become one condition if b then H1' else H2'. So no side needs the
   other's conditions, and in particular not its gas.

   A path ends at a halt (STOP, RETURN, REVERT, INVALID, ...), at a pc
   already on the path (a loop, but also a second call of an internal
   function, which the walk does not tell apart), at a jump whose target is still not a
   constant, at a CALL-class block, or at a pc without summaries. Only
   halts finish the run; the others leave a postcondition at that pc, and
   are listed. A jump target that a block reads off the stack (an
   internal return) is a constant once the path has pushed it, so internal
   functions are followed through, on their first call on the path.
   Conditions the walk cannot discharge stay in the triple's cond: those of
   a JUMPI side with no summary, say, or of a side whose other side turned
   out infeasible only further on. Paths that meet again are not shared:
   each is walked to its end, so the cost grows with the number of paths,
   not of blocks.
   ------------------------------------------------------------------------ *)

(* proved on first use, as b2w_lemma *)
val cond_cache = ref (NONE : thm option)
fun cond_lemma () =
  case !cond_cache of
    SOME th => th
  | NONE =>
      let val th = GENL [“b:bool”, “x:'a”, “y:'a”] (prove(
            “(b ==> ((if b then x else y) = x:'a)) /\
             (~b ==> ((if b then x else y) = y:'a))”,
            Cases_on `b` \\ REWRITE_TAC []))
      in cond_cache := SOME th; th end

(* |- (if b then x else y) = x under b, = y under ~b *)
fun cond_eq side b x y =
  let val th = ISPECL [b, x, y] (cond_lemma ())
  in if side then MP (CONJUNCT1 th) (ASSUME b)
     else MP (CONJUNCT2 th) (ASSUME (mk_neg b)) end

fun entry_pc th =
  case List.find (fn a => head_name a = "evm_PC") (stars (pre_of th)) of
    SOME a => (SOME (numSyntax.int_of_term (rand a)) handle HOL_ERR _ => NONE)
  | NONE => NONE

fun halted th =
  case post_value "evm_Exception" th of
    SOME t => sumSyntax.is_inr t
  | NONE => false

(* a CALL-class rule names its instruction in evm_Parsed, not in the code *)
fun is_call_block th =
  List.exists (fn a => head_name a = "evm_hide_Parsed") (stars (post_of th))

(* replace the hypotheses hs of th by the c that implies them
   (cth : [c] |- list_mk_conj hs) *)
fun replace_hyps hs cth th =
  foldl (fn (h, th) => PROVE_HYP h th) th (CONJ_LIST (length hs) cth)

fun conj_or_T [] = T
  | conj_or_T cs = list_mk_conj cs

(* |- ~b ==> c, for b and c the guards of the two sides *)
fun guard_imp cfg cf b c =
  let val tm = mk_imp (mk_neg b, c) in
    tautLib.TAUT_PROVE tm
    handle HOL_ERR _ => EQT_ELIM (simp_term cf tm)
    handle HOL_ERR _ => arith_decide tm
    handle HOL_ERR _ =>
      raise ERR "compose_region"
        ("cannot show the branches exhaustive: " ^ term_to_string tm)
  end

(* the instantiation making a part of one precondition the corresponding
   part of the other *)
fun unify_pres th1 th2 =
  let
    fun go (th1, th2) =
      let
        val ps1 = stars (pre_of th1) and ps2 = stars (pre_of th2)
        fun differ a2 =
          case List.find (fn a1 => aconv (resource a1) (resource a2)) ps1 of
            SOME a1 => if aconv a1 a2 then NONE else SOME (a1, a2)
          | NONE => NONE
      in
        case List.mapPartial differ ps2 of
          [] => (th1, th2)
        | (a1, a2) :: _ =>
            (case Lib.total (match_term a2) a1 of
               SOME (s, []) => go (th1, INST s th2)
             | _ =>
               case Lib.total (match_term a1) a2 of
                 SOME (s, []) => go (INST s th1, th2)
               | _ => raise ERR "compose_region"
                        ("preconditions differ: " ^ term_to_string a1 ^
                         " and " ^ term_to_string a2))
      end
  in go (th1, th2) end

(* merge the sides of a split with guard b (see above); base is the
   triple before the split *)
fun merge_sides base b ((th1, seen1), (th2, seen2)) =
  let
    (* side 2's own variables apart from side 1's *)
    val base_vs = thm_frees base
    val vs1 = thm_frees th1
    val clash = filter (fn v => tmem v vs1 andalso not (tmem v base_vs))
                       (thm_frees th2)
    val avoid = ref (vs1 @ thm_frees th2)
    val s = map (fn v => let val v' = variant (!avoid) v
                         in avoid := v' :: !avoid; v |-> v' end) clash
    val th2 = INST s th2
    (* a memory definition side 2 repeats is side 1's *)
    fun share th2 =
      let
        val defs1 = List.mapPartial mem_def_of (hyp th1)
        fun same (v2, t2) =
          if tmem v2 vs1 then NONE
          else Option.map (fn (v1, _) => v2 |-> v1)
                 (List.find (fn (_, t1) => aconv t1 t2) defs1)
      in
        case List.mapPartial same (List.mapPartial mem_def_of (hyp th2)) of
          [] => ([], th2)
        | r :: _ => let val (rs, th2') = share (INST [r] th2)
                    in (r :: rs, th2') end
      end
    val (shared, th2) = share th2
    val seen2 = map (subst shared) (map (subst s) seen2)
    (* the same precondition on both sides *)
    val (th1, th2) = unify_pres th1 th2
    fun missing th th' =
      filter (fn a => not (List.exists (fn x => aconv (resource x)
                                                     (resource a))
                                         (stars (pre_of th))))
             (stars (pre_of th'))
    val th1 = frame th1 (missing th1 th2)
    val th2 = frame th2 (missing th2 th1)
    val th2 = CONV_RULE (PRE_CONV (K (star_eq (pre_of th2) (pre_of th1)))) th2
    (* the same code *)
    val c1 = code_of th1 and c2 = code_of th2
    val c = pred_setSyntax.mk_union (c1, c2)
    val th1 = SPEC c2 (MATCH_MP SPEC_ADD_CODE th1)
    val th2 = MP (SPEC c (MATCH_MP SPEC_SUBSET_CODE th2))
                 (ISPECL [c2, c1] (CONJUNCT2 SUBSET_UNION))
    (* the conditions *)
    val h1 = filter (not o aconv b) (hyp th1)
    val h2 = filter (not o aconv (mk_neg b)) (hyp th2)
    val common = filter (fn h => tmem h h2) h1
    fun own hs = filter (fn h => not (tmem h common) andalso
                                 not (is_mem_def h)) hs
    val d1 = own h1 and d2 = own h2
    val k = mk_cond (b, conj_or_T d1, conj_or_T d2)
    val th1 = if List.null d1 then th1
              else replace_hyps d1 (EQ_MP (cond_eq true b (conj_or_T d1)
                                                (conj_or_T d2))
                                       (ASSUME k)) th1
    val th2 = if List.null d2 then th2
              else replace_hyps d2 (EQ_MP (cond_eq false b (conj_or_T d1)
                                                (conj_or_T d2))
                                       (ASSUME k)) th2
    (* the postcondition *)
    val q1 = post_of th1 and q2 = post_of th2
    val th1 = CONV_RULE (RAND_CONV (K (SYM (cond_eq true b q1 q2)))) th1
    val th2 = CONV_RULE (RAND_CONV (K (SYM (cond_eq false b q1 q2)))) th2
    val th = DISJ_CASES (SPEC b EXCLUDED_MIDDLE) th1 th2
    val seen = filter (fn h => tmem h (hyp th)) (seen1 @ seen2 @ [k])
  in (th, op_mk_set aconv seen) end

(* the code of a closed triple with each instruction once *)
fun dedup_code th =
  let
    val c = code_of th
    val elts = pred_setSyntax.strip_set c
    val elts' = op_mk_set aconv elts
  in
    if length elts' = length elts then th
    else
      let
        val c' = pred_setSyntax.mk_set elts'
        val sub = EQT_ELIM (REWRITE_CONV [INSERT_SUBSET, EMPTY_SUBSET,
                                          IN_INSERT]
                              (pred_setSyntax.mk_subset (c, c')))
      in MP (SPEC c' (MATCH_MP SPEC_SUBSET_CODE th)) sub end
  end

(* b decided by the guards of the splits before it on the path: a JUMPI
   testing again what an earlier one tested *)
fun decide [] b = NONE
  | decide guards b =
      let val eq = QCONV (SIMP_CONV bool_ss (map ASSUME guards)) b
          val r = rhs (concl eq)
      in if aconv r T orelse aconv r F then SOME eq else NONE end
      handle HOL_ERR _ => NONE

fun compose_region cfg sums start =
  let
    val cf = mk_code_facts cfg
    val table =
      foldl (fn (th, t) =>
               case entry_pc th of
                 SOME n => Redblackmap.insert (t, n,
                             getOpt (Redblackmap.peek (t, n), []) @ [th])
               | NONE => raise ERR "compose_region" "summary without a pc")
            (Redblackmap.mkDict Int.compare) sums
    val leaves = ref ([] : (int list * string) list)
    fun leaf path why (th, seen) =
      let
        val th1 = polish cfg cf th
        val th2 = th1 |> collapse is_gas_bound
                      |> collapse (is_stack_bound (stack_rest th1))
      in
        leaves := (rev path, why) :: !leaves;
        (th2, filter (fn h => tmem h (hyp th2)) (seen @ hyp_order seen th2))
      end
    fun step_one path =
      compose_step cfg cf "compose_region"
        ("after " ^ String.concatWith " " (map Int.toString (rev path)))
    fun walk path guards (th, seen) =
      if halted th then leaf path "halt" (th, seen)
      else
        case post_value "evm_PC" th of
          NONE => raise ERR "compose_region" "no evm_PC"
        | SOME t =>
          if not (numSyntax.is_numeral t) then
            leaf path ("jump to " ^ tm_str t) (th, seen)
          else
            let val n = numSyntax.int_of_term t in
              if mem n path then
                leaf path ("revisit " ^ Int.toString n) (th, seen)
              else
                case getOpt (Redblackmap.peek (table, n), []) of
                  [] => leaf path ("no summary at " ^ Int.toString n)
                             (th, seen)
                | rs =>
                  if List.exists is_call_block rs then
                    leaf path ("call at " ^ Int.toString n) (th, seen)
                  else
                    let
                      val path' = n :: path
                      val sides =
                        List.mapPartial
                          (fn r => SOME (step_one path' (th, seen) r)
                                   handle Infeasible_cond _ => NONE) rs
                    in
                      case sides of
                        [] => raise Infeasible_cond F
                      | [side] => walk path' guards side
                      | [side1, side2] => split path' guards th side1 side2
                      | _ => raise ERR "compose_region"
                               ("more than two summaries feasible at " ^
                                Int.toString n)
                    end
            end
    (* th composed with the two summaries at a JUMPI. The conditions they
       added are simplified first, with the values apply_rule kept
       abstract, so that the guard is readable and can be decided. *)
    and split path guards th side1 side2 =
      let
        fun simp_new (th', seen') =
          SOME (simp_hyps cfg cf (filter (fn h => not (tmem h (hyp th)))
                                         (hyp th')) th', seen')
          handle Infeasible_cond _ => NONE
      in
        case (simp_new side1, simp_new side2) of
          (NONE, NONE) => raise Infeasible_cond F
        | (SOME s1, NONE) => walk path guards s1
        | (NONE, SOME s2) => walk path guards s2
        | (SOME (th1, seen1), SOME (th2, seen2)) =>
          let
            val d1 = filter (fn h => not (tmem h (hyp th2))) (hyp th1)
            val d2 = filter (fn h => not (tmem h (hyp th1))) (hyp th2)
          in
            (* a side whose conditions the path already has is the one
               taken: the other's contradict them *)
            if List.null d1 then walk path guards (th1, seen1)
            else if List.null d2 then walk path guards (th2, seen2)
            else
              let
                val b = list_mk_conj d1
                val th1 = replace_hyps d1 (ASSUME b) th1
                (* side 2's conditions follow from ~b *)
                fun th2_neg () =
                  replace_hyps d2 (MP (guard_imp cfg cf b (conj_or_T d2))
                                      (ASSUME (mk_neg b))) th2
                fun try g side = SOME (walk path (g :: guards) side)
                                 handle Infeasible_cond _ => NONE
              in
                case decide guards b of
                  SOME eq =>
                    if aconv (rhs (concl eq)) T
                    then walk path guards (PROVE_HYP (EQT_ELIM eq) th1, seen1)
                    else walk path guards
                           (PROVE_HYP (EQF_ELIM eq) (th2_neg ()), seen2)
                | NONE =>
                  case (try b (th1, seen1),
                        try (mk_neg b) (th2_neg (), seen2)) of
                    (SOME r1, SOME r2) => merge_sides th b (r1, r2)
                  | (SOME r1, NONE) => r1
                  | (NONE, SOME r2) => r2
                  | (NONE, NONE) => raise Infeasible_cond F
              end
          end
      end
    val th0 = undisch_conds start
    val (th, seen) = walk [] [] (th0, hyp_order [] th0)
                     handle Infeasible_cond _ =>
                       raise ERR "compose_region" "no feasible path"
    val (th1, _, _) = uncurry close_conds (renumber_memory seen th)
  in (dedup_code th1, rev (!leaves)) end

end
