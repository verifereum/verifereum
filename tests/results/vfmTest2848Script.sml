open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2848Theory;
val () = new_theory "vfmTest2848";
val thyn = "vfmTestDefs2848";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
