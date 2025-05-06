open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1112Theory;
val () = new_theory "vfmTest1112";
val thyn = "vfmTestDefs1112";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
