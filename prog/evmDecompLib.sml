(* ------------------------------------------------------------------------
   evmDecompLib: certified block summaries of EVM runtime code.

   Given a contract's runtime code, summarize_code produces one theorem per
   basic block and exit, each a SPEC EVM_MODEL triple over the real semantics
   composed from the per-instruction rules of vfmProgTheory. Nothing here is
   trusted: every summary is proved by SPEC_REFL, SPEC_FRAME, SPEC_COMPOSE and
   SPEC_MOVE_COND from those rules, so a wrong hint or a bug in the composer
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
   parsed pc, which the code of a longer block would also claim.

   Summary format. For a block at pc n with d stack slots read and k left:

     SPEC EVM_MODEL
       (evm_Stack (s0::...::s(d-1)::rest) * evm_PC n * <other resources> *
        cond C * cond G)
       {(n,i0); ...}
       (evm_Stack (e0::...::e(k-1)::rest) * evm_PC x * <resources'>)

   - rest is never inspected: d is the depth the block reads (checked by the
     proof, which fails to reach this shape if d is too small).
   - each e_i, and every resource in the post, is a term over the s_i and
     the entry resources (p.caller, the memory m, the rollback state rb, ...):
     no intermediate stack survives.
   - C is the condition the block needs to run: stack-depth bound, ISL e,
     j = NONE, p.code/p.parsed equal to the contract's code (when a jump or a
     code-reading instruction needs it), JUMPI conditions, static-context
     facts, access-list facts.
   - G is the gas layer: every conjunct that mentions p.gasLimit. The
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
               simps : thm list}

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

fun instructions (cfg : config) =
  #parsed_eq cfg |> concl |> rhs
  |> find_terms finite_mapSyntax.is_fupdate
  |> map (fn tm => pairSyntax.dest_pair (rand tm))
  |> map (fn (n, tm) => (numSyntax.int_of_term n, tm))
  |> Listsort.sort (fn ((n, _), (m, _)) => Int.compare (n, m))

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

fun block_instructions cfg starts start =
  let
    val tbl = Redblackmap.fromList Int.compare (instructions cfg)
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

val word_of_bytes_conv =
  REWR_CONV (SRULE [FUN_EQ_THM] (GSYM byteTheory.word_of_bytes_le_def))
  THENC cv_transLib.cv_eval

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

fun simp_conv (cfg : config) =
  SIMP_CONV (srw_ss() ++ word_of_bytes_ss) (base_simps () @ #simps cfg)

(* Facts about the contract's code. A condition or value mentioning p.code or
   p.parsed is rewritten under the assumption that they are the contract's
   code and parsed code; that assumption becomes a condition of the block. *)
type code_facts =
  {code_c : term, parsed_c : term, length_th : thm,
   flookup : term -> thm}

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
     flookup = flookup}
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
fun simp_term cfg (cf : code_facts) tm =
  let
    val assums = code_assumptions cf tm
    val c1 = (if List.null assums then ALL_CONV
              else PURE_REWRITE_CONV assums
                   THENC PURE_REWRITE_CONV [#length_th cf])
             THENC DEPTH_CONV (flookup_conv cf)
  in QCONV (c1 THENC simp_conv cfg) tm end

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
    val eq = simp_term cfg cf c
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

(* a hypothesis v = t (or (v1,...,vn) = t) defining variables local to one
   rule: they are instantiated away *)
fun local_def fixed c =
  let
    val (l, r) = dest_eq c
    fun local_var v = is_var v andalso not (tmem v fixed)
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
    fun frame th [] = th
      | frame th xs = SPEC (list_mk_star xs assertion_ty)
                           (MATCH_MP SPEC_FRAME th)
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
    val r6 = CONV_RULE (RAND_CONV (simp_term cfg cf)) r5
  in compose th (INST later r6) end

fun mentions_gas t =
  can (find_term (fn x => can (match_term gaslimit_pat) x)) t

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
    val th2 = CONV_RULE (RAND_CONV (simp_term cfg cf)) th1
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

(* keep the strongest of a family of bounds, discharging the others *)
fun collapse pred th =
  let
    val hs = filter pred (hyp th)
    fun imp (t, m) = arith_decide (mk_imp (m, t))
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
    val (gas, cnd) = partition mentions_gas order
    val th2 = th1 |> move_cond cnd |> move_cond gas
                  |> CONV_RULE (RATOR_CONV (RAND_CONV code_norm)
                                THENC PRE_CONV (PURE_REWRITE_CONV
                                                  [STAR_ASSOC]))
    val _ = if List.null (hyp th2) then ()
            else raise ERR "close_conds" "hypotheses left"
  in (th2, cnd, gas) end

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

fun compose_blocks cfg [] = raise ERR "compose_blocks" "no summaries"
  | compose_blocks cfg (th :: ths) =
  let
    val cf = mk_code_facts cfg
    val th0 = undisch_conds th
    fun go ((i, r), (th, seen)) =
      let
        val theta = widen_stack th r
        val seen = map (subst theta) seen
        val th' = apply_rule cfg cf I r (INST theta th)
                  handle HOL_ERR e =>
                    raise ERR "compose_blocks"
                      ("summary " ^ Int.toString i ^ ": " ^
                       top_function_of e ^ ": " ^ message_of e)
      in (th', seen @ hyp_order seen th') end
    val numbered = ListPair.zip (List.tabulate (length ths, fn i => i + 1), ths)
    val (th, seen) = foldl go (th0, hyp_order [] th0) numbered
  in #1 (close_conds seen (polish cfg cf th)) end
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
          in (th', effs @ effects_of_step pc_inst th th',
              seen @ hyp_order seen th')
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
        val th1 = polish cfg cf th0
        val (th3, cnd, gas) = close_conds seen th1
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
    val insts = block_instructions cfg starts entry
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

end
