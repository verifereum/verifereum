signature vfmTestLib = sig
  val mk_prove_test : string -> int * (int -> Thm.thm)
  val prep_test: string -> int -> string * Term.term * (Tactic.goal, Thm.thm) Tactical.gentactic
end
