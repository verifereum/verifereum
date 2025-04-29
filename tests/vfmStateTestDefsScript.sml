open HolKernel vfmTestLib

val () = new_theory "vfmStateTestDefs";

val defs = mapi define_state_test $ get_all_state_tests ();

val () = export_theory_no_docs ();
