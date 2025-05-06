open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1260Theory;
val () = new_theory "vfmTest1260";
val thyn = "vfmTestDefs1260";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
