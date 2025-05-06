open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1527Theory;
val () = new_theory "vfmTest1527";
val thyn = "vfmTestDefs1527";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
