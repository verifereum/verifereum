open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2143Theory;
val () = new_theory "vfmTest2143";
val thyn = "vfmTestDefs2143";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
