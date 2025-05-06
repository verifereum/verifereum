open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1720Theory;
val () = new_theory "vfmTest1720";
val thyn = "vfmTestDefs1720";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
