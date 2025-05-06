open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1493Theory;
val () = new_theory "vfmTest1493";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1493") $ get_result_defs "vfmTestDefs1493";
val () = export_theory_no_docs ();
