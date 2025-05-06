open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1923Theory;
val () = new_theory "vfmTest1923";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1923") $ get_result_defs "vfmTestDefs1923";
val () = export_theory_no_docs ();
