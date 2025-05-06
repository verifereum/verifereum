open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1348Theory;
val () = new_theory "vfmTest1348";
val thyn = "vfmTestDefs1348";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
