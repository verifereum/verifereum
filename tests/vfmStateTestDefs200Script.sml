open HolKernel vfmTestLib

val () = new_theory "vfmStateTestDefs200";

val defs = define_state_tests 100 200;

val () = export_theory_no_docs ();
