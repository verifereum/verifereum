open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2001Theory;
val () = new_theory "vfmTest2001";
val thyn = "vfmTestDefs2001";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
