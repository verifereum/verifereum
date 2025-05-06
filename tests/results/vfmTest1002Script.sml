open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1002Theory;
val () = new_theory "vfmTest1002";
val thyn = "vfmTestDefs1002";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
