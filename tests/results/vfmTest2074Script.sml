open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2074Theory;
val () = new_theory "vfmTest2074";
val thyn = "vfmTestDefs2074";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
