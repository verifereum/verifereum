signature evmDecompLib =
sig

  include Abbrev

  (* What the library needs to know about one contract. code_eq is
     `code = [bytes]` for a constant code; parsed_eq is
     `parsed = FEMPTY |+ ...`, the evaluated `parse_code 0 FEMPTY code` for
     a constant parsed. hints are extra block starts (pcs); simps are extra
     rewrites used when simplifying stack values and side conditions.
     strip_metadata leaves out the compiler's CBOR metadata at the end of
     the code (see metadata_start). *)
  type config = {code_eq : thm, parsed_eq : thm, hints : int list,
                 simps : thm list, strip_metadata : bool}

  (* no hints, no simps, metadata stripped *)
  val default_config : thm -> thm -> config

  (* the pc where the CBOR metadata trailer begins, if the code ends with
     one: a non-empty CBOR map or array, followed by its length in two
     big-endian bytes (solc's layout, the length excluding those two bytes,
     or Vyper's, including them). The item must parse as CBOR and end
     exactly at the length bytes. *)
  val metadata_start : config -> int option

  datatype exit =
      Jump of term          (* JUMP; the target pc, a numeral when constant *)
    | JumpITaken of term    (* JUMPI taken; target pc *)
    | JumpISkip of int      (* JUMPI not taken; the next pc *)
    | FallThrough of int    (* runs into the next block start *)
    | Halt of string        (* STOP/RETURN/REVERT/...; the rule's label *)
    | Call of string        (* CALL-class terminator; the rule's label *)

  type effect = {pc : int, inst : term, resource : string, value : term}

  type block_summary =
    {entry : int, variant : string, exit : exit,
     depth : int, height : int,
     entry_stack : term list, exit_stack : term list,
     effects : effect list, cond : term list, gas : term list,
     code : (int * term) list}

  type failure = {entry : int, variant : string, pc : int, inst : term,
                  reason : string}

  (* Infeasible: a side condition of a rule on the way simplifies to false,
     so no rule describes the run. That is a decided JUMPI condition, but
     also a jump to a pc that is not a JUMPDEST, which the EVM runs and
     halts with an exception: the rules describe non-exceptional steps. *)
  datatype outcome = Summary of block_summary * thm
                   | Infeasible of {entry : int, variant : string,
                                    cond : term}
                   | Failed of failure

  (* the rule table: opcode constructor name |-> (label, SPEC theorem);
     several rules for one opcode only for a terminator, one summary each *)
  val rules_for : term -> (string * thm) list
  val set_rules : string -> (string * thm) list -> unit
  val add_rules : string -> (string * thm) list -> unit

  val instructions : config -> (int * term) list
  val block_starts : config -> int list
  val block_instructions : config -> int list -> int -> (int * term) list

  val summarize_block : config -> int -> outcome list
  val summarize_code : config -> outcome list
  val summaries : outcome list -> (block_summary * thm) list

  (* the summaries of a path, composed; each block's entry is instantiated
     from the previous exit, widening the previous stack when a block reads
     deeper than the previous one leaves visible *)
  val compose_blocks : config -> thm list -> thm
  (* hides the gas used in the post; compose_blocks refuses a hidden
     resource that a later summary reads, so only for the last summary *)
  val drop_gas : thm -> thm
  (* a summary's memory terms are abbreviated as variables mem<n>, each
     defined by a conjunct mem<n> = t of its cond C; this instantiates every
     mem<n> to its definition and drops those conjuncts *)
  val inline_memory : thm -> thm

  (* compose_region cfg summaries th: every path from th's exit through
     the summaries, composed into one triple, a JUMPI whose guard the path
     leaves open giving the postcondition if b then Q1 else Q2. Also
     returns each path, as the entry pcs of its summaries, and how it ends:
     "halt", or where the walk stopped ("revisit n" for a pc already on
     the path, "jump to t", "call at n", "no summary at n"). Conditions it
     cannot discharge, such as those of a branch with no summary, stay in
     the triple's cond. *)
  val compose_region : config -> thm list -> thm ->
                       thm * (int list * string) list

  val exit_to_string : exit -> string
  val block_summary_to_string : block_summary -> string
  val outcome_to_string : outcome -> string

end
