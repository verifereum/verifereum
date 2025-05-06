open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1073Theory;
val () = new_theory "vfmTest1073";
val thyn = "vfmTestDefs1073";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
