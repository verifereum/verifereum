open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1922Theory;
val () = new_theory "vfmTest1922";
val thyn = "vfmTestDefs1922";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
