open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2662Theory;
val () = new_theory "vfmTest2662";
val thyn = "vfmTestDefs2662";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
