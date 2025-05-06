open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2271Theory;
val () = new_theory "vfmTest2271";
val thyn = "vfmTestDefs2271";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
