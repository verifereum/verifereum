open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2477Theory;
val () = new_theory "vfmTest2477";
val thyn = "vfmTestDefs2477";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
