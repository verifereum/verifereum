open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1493Theory;
val () = new_theory "vfmTest1493";
val thyn = "vfmTestDefs1493";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
