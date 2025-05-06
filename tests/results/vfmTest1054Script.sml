open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1054Theory;
val () = new_theory "vfmTest1054";
val thyn = "vfmTestDefs1054";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
