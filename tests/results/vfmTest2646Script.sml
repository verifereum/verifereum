open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2646Theory;
val () = new_theory "vfmTest2646";
val thyn = "vfmTestDefs2646";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
