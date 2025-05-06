open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2832Theory;
val () = new_theory "vfmTest2832";
val thyn = "vfmTestDefs2832";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
