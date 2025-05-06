open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2698Theory;
val () = new_theory "vfmTest2698";
val thyn = "vfmTestDefs2698";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
