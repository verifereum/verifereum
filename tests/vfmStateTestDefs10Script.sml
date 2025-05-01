open HolKernel vfmTestLib

val () = new_theory "vfmStateTestDefs10";

val defs = define_state_tests 0 10;

val () = export_theory_no_docs ();
