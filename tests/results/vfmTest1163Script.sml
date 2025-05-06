open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1163Theory;
val () = new_theory "vfmTest1163";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1163") $ get_result_defs "vfmTestDefs1163";
val () = export_theory_no_docs ();
