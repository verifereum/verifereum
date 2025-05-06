open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1114Theory;
val () = new_theory "vfmTest1114";
val thyn = "vfmTestDefs1114";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
