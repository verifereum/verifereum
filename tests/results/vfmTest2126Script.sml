open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2126Theory;
val () = new_theory "vfmTest2126";
val thyn = "vfmTestDefs2126";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
