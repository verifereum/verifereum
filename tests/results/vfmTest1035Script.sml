open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1035Theory;
val () = new_theory "vfmTest1035";
val thyn = "vfmTestDefs1035";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
