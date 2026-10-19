Theory vfmUncheckedEmit
Ancestors vfmTestRun
Libs cv_transLib cv_repLib cv_typeLib cv_miscLib EmitML vfmTestAuxLib

(* This theory is a build-time code generator only.  Its generated ML contains
   the translated equations, never a call to cv_eval or a HOL term interpreter. *)
val () = holbuild_extra_outputs ["vfmUncheckedML.sml", "vfmUncheckedML.sig"];

val cv_ty = cvSyntax.cv;
val module_name = "vfmUnchecked";

fun argument_types ty =
  case total dom_rng ty of
    NONE => []
  | SOME (a, b) => a :: argument_types b;

(* Ask the translator for the representation of each public operation.  Replace
   precisely the encodings of its symbolic inputs with native CV arguments.
   This also obtains the record layouts from the translator, rather than
   duplicating its constructor-tag/field-order conventions in the runner. *)
fun native_expression args tm = let
  val rep = cv_repLib.cv_rep_for [] tm
  val body = cv_miscLib.cv_rep_cv_tm (concl rep)
  val cvs = map (fn v => mk_var ("arg_" ^ fst (dest_var v), cv_ty)) args
  val replacements = map2 (fn v => fn c =>
    mk_comb (cv_typeLib.from_term_for (type_of v), v) |-> c) args cvs
  val body = subst replacements body
  val _ = List.all (fn v => List.exists (aconv v) cvs) (free_vars body)
          orelse raise Fail "unchecked export: an input encoding was not eliminated"
  in (cvs, body) end;

fun make_export name args tm = let
  val (cvs, body) = native_expression args tm
  val fnvar = mk_var ("unchecked_" ^ name, type_of (list_mk_abs (cvs, body)))
  val def = new_definition ("unchecked_" ^ name ^ "_def",
                           mk_eq (list_mk_comb (fnvar, cvs), body))
  in (name, cvs, body, def) end;

fun operation (name, arity, tm) = let
  (* State values are logically functions.  Their result arrows are not extra
     native arguments: the CV representation stores the complete finite state. *)
  val args = mapi (fn i => fn ty => mk_var ("x" ^ Int.toString i, ty))
                  (List.take (argument_types (type_of tm), arity))
  in make_export name args (list_mk_comb (tm, args)) end;

val operations = map operation
  [("run_test", 6, ``run_test``),
   ("empty_storage", 0, ``empty_storage``),
   ("update_storage", 3, ``update_storage``),
   ("empty_accounts", 0, ``empty_accounts``),
   ("update_account", 3, ``update_account``),
   ("valid_block", 2, ``ValidBlock``),
   ("invalid_block", 3, ``InvalidBlock``)];

fun record_export (name, ty) = let
  val fields = TypeBase.fields_of ty
  val args = map (fn (field, {ty, ...}) => mk_var (field, ty)) fields
  val tm = TypeBase.mk_record (ty, map2 (fn (field, _) => fn v => (field, v))
                                             fields args)
  in (map #1 fields, make_export name args tm) end;

val records = map record_export
  [("account", ``:account_state``), ("transaction", ``:transaction``),
   ("block", ``:block``), ("withdrawal", ``:withdrawal``),
   ("access_list_entry", ``:access_list_entry``),
   ("authorization", ``:authorization``)];
val exports = operations @ map #2 records;

val roots = foldr (fn ((_, _, body, _), rest) => cvSyntax.mk_cv_pair (body, rest))
                  (cvSyntax.mk_cv_num (numSyntax.term_of_int 0)) exports;
val equations = cv_transLib.cv_eqs_for roots;

fun equation_const th = fst (strip_comb (lhs (concl (SPEC_ALL th))));
fun constant_key c = let val {Thy, Name, ...} = dest_thy_const c
                    in Thy ^ "$" ^ Name end;
val equation_table = mapi (fn i => fn th =>
  (constant_key (equation_const th), i)) equations;
fun index_for c = List.find (fn (key, _) => key = constant_key c) equation_table;
fun dependencies th =
  List.mapPartial (Option.map #2 o index_for)
    (find_terms is_const (rhs (concl (SPEC_ALL th))));

(* cv_eqs_for returns a dependency closure, not a topological ordering.  Tarjan
   groups mutually recursive equations and emits dependencies before callers. *)
val count = length equations;
val edges = Vector.fromList (map dependencies equations);
val indices = Array.array (count, ~1);
val lowlinks = Array.array (count, ~1);
val on_stack = Array.array (count, false);
val next_index = ref 0;
val stack = ref ([] : int list);
val groups = ref ([] : int list list);
fun visit v = let
  val index = !next_index
  val () = next_index := index + 1
  val () = Array.update (indices, v, index)
  val () = Array.update (lowlinks, v, index)
  val () = Array.update (on_stack, v, true)
  val () = stack := v :: !stack
  fun edge w =
    if Array.sub (indices, w) = ~1 then
      (visit w;
       Array.update (lowlinks, v,
         Int.min (Array.sub (lowlinks, v), Array.sub (lowlinks, w))))
    else if Array.sub (on_stack, w) then
      Array.update (lowlinks, v,
        Int.min (Array.sub (lowlinks, v), Array.sub (indices, w)))
    else ()
  val () = List.app edge (Vector.sub (edges, v))
  fun pop acc = case !stack of
    [] => raise Fail "unchecked export: empty dependency stack"
  | w :: rest =>
      (stack := rest; Array.update (on_stack, w, false);
       if w = v then w :: acc else pop (w :: acc))
  in
    if Array.sub (lowlinks, v) = index then groups := pop [] :: !groups else ()
  end;
val () = List.app (fn i => if Array.sub (indices, i) = ~1 then visit i else ())
                   (List.tabulate (count, fn i => i));
val equation_vector = Vector.fromList equations;
val ordered_equations = map (LIST_CONJ o map (fn i => Vector.sub (equation_vector, i)))
                            (rev (!groups));

(* EmitML installs names for definitions itself.  CV record accessors can have
   dots in their HOL names, so introduce definitional aliases with legal,
   unique ML identifiers before handing the equations to EmitML. *)
val alias_rewrites = mapi (fn i => fn th => let
  val c = equation_const th
  val name = "code_" ^ Int.toString i
  val def = new_definition (name ^ "_alias",
                           mk_eq (mk_var (name, type_of c), c))
  in SYM def end) equations;
fun map_constant constructor name c =
  ConstMapML.prim_insert (c, (constructor, module_name, name, type_of c));
val () = List.app (fn name => map_constant false name
    (prim_mk_const {Thy = "cv", Name = name}))
  ["c2b", "cv_fst", "cv_snd", "cv_ispair", "cv_add", "cv_sub", "cv_mul",
   "cv_div", "cv_mod", "cv_lt", "cv_eq"];
val () = List.app (fn name => map_constant true name
    (prim_mk_const {Thy = "cv", Name = name})) ["Num", "Pair"];

(* A strict ML function for cv_if would evaluate both branches, including
   recursive calls in the unused branch.  Rewriting to HOL COND lets EmitML's
   dedicated conditional printer produce a genuinely lazy ML if-expression. *)
fun emitted_equation th =
  EmitML.DEFN_NOSIG
    (PURE_REWRITE_RULE (cvTheory.cv_if_def0 :: alias_rewrites) th);

fun cv_arrow args = String.concatWith " -> " (map (K "cv") args @ ["cv"]);
fun public_operation (name, args, _, _) =
  [EmitML.MLSIG ("val " ^ name ^ " : " ^ cv_arrow args ^ "\n"),
   EmitML.MLSTRUCT ("val " ^ name ^ " = unchecked_" ^ name ^ "\n")];
fun public_record (fields, (name, _, _, _)) =
  [EmitML.MLSIG ("val " ^ name ^ " : {" ^
     String.concatWith ", " (map (fn f => f ^ " : cv") fields) ^ "} -> cv\n"),
   EmitML.MLSTRUCT ("fun " ^ name ^ " {" ^ String.concatWith ", " fields ^
     "} = unchecked_" ^ name ^ " " ^ String.concatWith " " fields ^ "\n")];

(* Derive result tags from the same representation database.  Only formatting
   is native: it matches vfmTestResultLib.test_result_to_string exactly. *)
fun result_case constructor = let
  val args = mapi (fn i => fn ty => mk_var ("result" ^ Int.toString i, ty))
                  (argument_types (type_of constructor))
  val (_, encoded) = native_expression args (list_mk_comb (constructor, args))
  val tag = if null args then cvSyntax.dest_cv_num encoded
            else cvSyntax.dest_cv_num (fst (cvSyntax.dest_cv_pair encoded))
  val number = Arbnum.toString (numSyntax.dest_numeral tag)
  val name = #Name (dest_thy_const constructor)
  val suffix = case args of
      [] => ""
    | [arg] => if type_of arg = ``:string`` then
                 " ^ \" \" ^ string_of_cv payload"
               else " ^ \" \" ^ hex_of_cv payload"
    | _ => raise Fail "unchecked export: unsupported result constructor arity"
  in (null args, "if tag = Arbnum.fromString \"" ^ number ^ "\" then \"" ^
                  name ^ "\"" ^ suffix ^ " else ") end;
val result_cases = map result_case (TypeBase.constructors_of ``:test_result``);
fun result_branches nullary =
  String.concat (map #2 (filter (fn (n, _) => n = nullary) result_cases)) ^
  "raise Fail \"invalid CV test result tag\"";
val result_source =
  "infix 6 ^\nfun result_string value = case value of\n" ^
  "  Num tag => " ^ result_branches true ^ "\n" ^
  "| Pair (Num tag, payload) => " ^ result_branches false ^ "\n" ^
  "| _ => raise Fail \"invalid CV test result\"\n";

(* Theory builds emit into their staging/current source directory.  Loading
   the script from the project root must not leave duplicate modules there. *)
val output_dir =
  if (OS.FileSys.access ("vfmUncheckedEmitScript.sml", [OS.FileSys.A_READ])
      handle OS.SysErr _ => false) then "."
  else vfmTestAuxLib.test_path "";
val () = EmitML.emitML output_dir (module_name,
  [EmitML.MLSIG "datatype cv = datatype vfmUncheckedRuntime.cv\n",
   EmitML.MLSTRUCT "open vfmUncheckedRuntime\n"] @
  map emitted_equation ordered_equations @
  map (emitted_equation o #4) exports @
  List.concat (map public_operation operations) @
  List.concat (map public_record records) @
  [EmitML.MLSIG "val result_string : cv -> string\n",
   EmitML.MLSTRUCT result_source]);
