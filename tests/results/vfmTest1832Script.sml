open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1832Theory;
val () = new_theory "vfmTest1832";
val thyn = "vfmTestDefs1832";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
