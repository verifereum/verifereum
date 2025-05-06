open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1376Theory;
val () = new_theory "vfmTest1376";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1376") $ get_result_defs "vfmTestDefs1376";
val () = export_theory_no_docs ();
