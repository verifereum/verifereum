open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1621Theory;
val () = new_theory "vfmTest1621";
val thyn = "vfmTestDefs1621";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
