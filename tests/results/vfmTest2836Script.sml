open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2836Theory;
val () = new_theory "vfmTest2836";
val thyn = "vfmTestDefs2836";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
