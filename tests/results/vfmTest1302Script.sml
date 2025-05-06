open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1302Theory;
val () = new_theory "vfmTest1302";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1302") $ get_result_defs "vfmTestDefs1302";
val () = export_theory_no_docs ();
