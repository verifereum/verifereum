open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1199Theory;
val () = new_theory "vfmTest1199";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1199") $ get_result_defs "vfmTestDefs1199";
val () = export_theory_no_docs ();
