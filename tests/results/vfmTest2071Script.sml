open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2071Theory;
val () = new_theory "vfmTest2071";
val thyn = "vfmTestDefs2071";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
