open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1133Theory;
val () = new_theory "vfmTest1133";
val thyn = "vfmTestDefs1133";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
