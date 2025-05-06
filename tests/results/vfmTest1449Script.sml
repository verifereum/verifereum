open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1449Theory;
val () = new_theory "vfmTest1449";
val thyn = "vfmTestDefs1449";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
