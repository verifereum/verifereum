open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1722Theory;
val () = new_theory "vfmTest1722";
val thyn = "vfmTestDefs1722";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
