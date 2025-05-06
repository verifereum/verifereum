open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1717Theory;
val () = new_theory "vfmTest1717";
val thyn = "vfmTestDefs1717";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
