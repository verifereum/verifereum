open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1365Theory;
val () = new_theory "vfmTest1365";
val thyn = "vfmTestDefs1365";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
