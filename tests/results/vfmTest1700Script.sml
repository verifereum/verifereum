open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1700Theory;
val () = new_theory "vfmTest1700";
val thyn = "vfmTestDefs1700";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
