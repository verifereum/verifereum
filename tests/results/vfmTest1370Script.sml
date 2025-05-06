open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1370Theory;
val () = new_theory "vfmTest1370";
val thyn = "vfmTestDefs1370";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
