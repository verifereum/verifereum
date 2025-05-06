open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2387Theory;
val () = new_theory "vfmTest2387";
val thyn = "vfmTestDefs2387";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
