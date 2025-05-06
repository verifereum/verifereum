open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1829Theory;
val () = new_theory "vfmTest1829";
val thyn = "vfmTestDefs1829";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
