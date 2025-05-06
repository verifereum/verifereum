open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1074Theory;
val () = new_theory "vfmTest1074";
val thyn = "vfmTestDefs1074";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
