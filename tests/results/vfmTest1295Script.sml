open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1295Theory;
val () = new_theory "vfmTest1295";
val thyn = "vfmTestDefs1295";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
