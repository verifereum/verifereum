open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1598Theory;
val () = new_theory "vfmTest1598";
val thyn = "vfmTestDefs1598";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
