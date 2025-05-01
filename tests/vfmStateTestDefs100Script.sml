open HolKernel vfmTestLib

val () = new_theory "vfmStateTestDefs100";

val defs = define_state_tests 10 100;

val () = export_theory_no_docs ();
