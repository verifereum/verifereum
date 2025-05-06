open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1061Theory;
val () = new_theory "vfmTest1061";
val thyn = "vfmTestDefs1061";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
