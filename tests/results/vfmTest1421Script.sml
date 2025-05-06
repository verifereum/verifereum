open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1421Theory;
val () = new_theory "vfmTest1421";
val thyn = "vfmTestDefs1421";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
