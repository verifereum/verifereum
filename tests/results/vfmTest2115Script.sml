open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2115Theory;
val () = new_theory "vfmTest2115";
val thyn = "vfmTestDefs2115";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
