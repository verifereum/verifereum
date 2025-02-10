signature vfmTestLib = sig
  val mk_prove_test : string -> int * (int -> Thm.thm)
  val mk_tactic : (Tactic.goal, Thm.thm) Tactical.gentactic
  val prove_test : string -> string list -> int -> Thm.thm
  val prep_test: string -> string list -> int -> string * Term.term * (Tactic.goal, Thm.thm) Tactical.gentactic
end
