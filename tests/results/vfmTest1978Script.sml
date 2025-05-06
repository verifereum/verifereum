open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1978Theory;
val () = new_theory "vfmTest1978";
val thyn = "vfmTestDefs1978";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
