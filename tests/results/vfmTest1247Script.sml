open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1247Theory;
val () = new_theory "vfmTest1247";
val thyn = "vfmTestDefs1247";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
