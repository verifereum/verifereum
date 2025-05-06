open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2595Theory;
val () = new_theory "vfmTest2595";
val thyn = "vfmTestDefs2595";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
