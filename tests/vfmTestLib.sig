signature vfmTestLib = sig

  datatype 'a TestTree =
    TestDir of string * ('a TestTree) list
  | TestFixture of 'a

  val collect_fixtures : string -> string TestTree;


  datatype TestResult = TestPass | TestFail | TestPending | TestTimeout

  (* val runWithTimeout : (unit -> TestResult) -> LargeInt.int -> TestResult; *)

(*  *)
  val mk_prove_test : string -> int * (int -> Thm.thm)
  val prep_test: string -> int -> string * Term.term * (Tactic.goal, Thm.thm) Tactical.gentactic
  val export_theory_no_docs: unit -> unit
end
