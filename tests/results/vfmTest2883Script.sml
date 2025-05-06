open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2883Theory;
val () = new_theory "vfmTest2883";
val thyn = "vfmTestDefs2883";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
