open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1353Theory;
val () = new_theory "vfmTest1353";
val thyn = "vfmTestDefs1353";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
