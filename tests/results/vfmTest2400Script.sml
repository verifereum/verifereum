open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2400Theory;
val () = new_theory "vfmTest2400";
val thyn = "vfmTestDefs2400";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
