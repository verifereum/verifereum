open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1539Theory;
val () = new_theory "vfmTest1539";
val thyn = "vfmTestDefs1539";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
