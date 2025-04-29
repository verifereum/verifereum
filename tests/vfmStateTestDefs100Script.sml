open HolKernel vfmTestLib

val () = new_theory "vfmStateTestDefs100";

val defs = define_state_tests 0 100;

val () = export_theory_no_docs ();
