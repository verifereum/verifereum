open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1080Theory;
val () = new_theory "vfmTest1080";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1080") $ get_result_defs "vfmTestDefs1080";
val () = export_theory_no_docs ();
