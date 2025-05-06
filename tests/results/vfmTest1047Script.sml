open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1047Theory;
val () = new_theory "vfmTest1047";
val thyn = "vfmTestDefs1047";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
