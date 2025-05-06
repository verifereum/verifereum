open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2522Theory;
val () = new_theory "vfmTest2522";
val thyn = "vfmTestDefs2522";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
