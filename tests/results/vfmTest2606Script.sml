open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2606Theory;
val () = new_theory "vfmTest2606";
val thyn = "vfmTestDefs2606";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
