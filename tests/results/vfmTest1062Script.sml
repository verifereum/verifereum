open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1062Theory;
val () = new_theory "vfmTest1062";
val thyn = "vfmTestDefs1062";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
