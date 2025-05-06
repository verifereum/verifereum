open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2792Theory;
val () = new_theory "vfmTest2792";
val thyn = "vfmTestDefs2792";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
