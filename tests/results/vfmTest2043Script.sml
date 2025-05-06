open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2043Theory;
val () = new_theory "vfmTest2043";
val thyn = "vfmTestDefs2043";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
