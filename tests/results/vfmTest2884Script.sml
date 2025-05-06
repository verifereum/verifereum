open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2884Theory;
val () = new_theory "vfmTest2884";
val thyn = "vfmTestDefs2884";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
