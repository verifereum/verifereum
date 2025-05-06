open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2428Theory;
val () = new_theory "vfmTest2428";
val thyn = "vfmTestDefs2428";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
