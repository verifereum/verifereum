open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1002Theory;
val () = new_theory "vfmTest1002";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1002") $ get_result_defs "vfmTestDefs1002";
val () = export_theory_no_docs ();
