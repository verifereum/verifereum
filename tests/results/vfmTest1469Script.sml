open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1469Theory;
val () = new_theory "vfmTest1469";
val thyn = "vfmTestDefs1469";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
