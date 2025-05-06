open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1647Theory;
val () = new_theory "vfmTest1647";
val thyn = "vfmTestDefs1647";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
