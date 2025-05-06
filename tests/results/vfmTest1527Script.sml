open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1527Theory;
val () = new_theory "vfmTest1527";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1527") $ get_result_defs "vfmTestDefs1527";
val () = export_theory_no_docs ();
