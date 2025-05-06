open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1148Theory;
val () = new_theory "vfmTest1148";
val thyn = "vfmTestDefs1148";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
