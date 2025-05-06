open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1217Theory;
val () = new_theory "vfmTest1217";
val thyn = "vfmTestDefs1217";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
