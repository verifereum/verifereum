open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1964Theory;
val () = new_theory "vfmTest1964";
val thyn = "vfmTestDefs1964";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
