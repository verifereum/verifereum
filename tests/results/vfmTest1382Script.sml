open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1382Theory;
val () = new_theory "vfmTest1382";
val thyn = "vfmTestDefs1382";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
