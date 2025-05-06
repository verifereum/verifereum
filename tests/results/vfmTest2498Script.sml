open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2498Theory;
val () = new_theory "vfmTest2498";
val thyn = "vfmTestDefs2498";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
