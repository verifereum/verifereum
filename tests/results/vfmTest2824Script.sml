open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2824Theory;
val () = new_theory "vfmTest2824";
val thyn = "vfmTestDefs2824";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
