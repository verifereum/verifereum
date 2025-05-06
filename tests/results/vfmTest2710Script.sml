open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2710Theory;
val () = new_theory "vfmTest2710";
val thyn = "vfmTestDefs2710";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
