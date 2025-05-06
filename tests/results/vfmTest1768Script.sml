open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1768Theory;
val () = new_theory "vfmTest1768";
val thyn = "vfmTestDefs1768";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
