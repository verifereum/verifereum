open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1874Theory;
val () = new_theory "vfmTest1874";
val thyn = "vfmTestDefs1874";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
