open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1522Theory;
val () = new_theory "vfmTest1522";
val thyn = "vfmTestDefs1522";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
