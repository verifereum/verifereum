open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1150Theory;
val () = new_theory "vfmTest1150";
val thyn = "vfmTestDefs1150";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
