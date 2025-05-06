open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2443Theory;
val () = new_theory "vfmTest2443";
val thyn = "vfmTestDefs2443";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
