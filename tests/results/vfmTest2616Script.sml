open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2616Theory;
val () = new_theory "vfmTest2616";
val thyn = "vfmTestDefs2616";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
