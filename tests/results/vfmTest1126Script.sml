open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1126Theory;
val () = new_theory "vfmTest1126";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1126") $ get_result_defs "vfmTestDefs1126";
val () = export_theory_no_docs ();
