open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1986Theory;
val () = new_theory "vfmTest1986";
val thyn = "vfmTestDefs1986";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
