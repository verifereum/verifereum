open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1499Theory;
val () = new_theory "vfmTest1499";
val thyn = "vfmTestDefs1499";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
