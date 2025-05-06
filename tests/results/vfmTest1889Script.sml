open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1889Theory;
val () = new_theory "vfmTest1889";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1889") $ get_result_defs "vfmTestDefs1889";
val () = export_theory_no_docs ();
