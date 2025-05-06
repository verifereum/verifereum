open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1066Theory;
val () = new_theory "vfmTest1066";
val thyn = "vfmTestDefs1066";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
