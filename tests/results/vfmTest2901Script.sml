open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2901Theory;
val () = new_theory "vfmTest2901";
val thyn = "vfmTestDefs2901";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
