open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0277Theory;
val () = new_theory "vfmTest0277";
val thyn = "vfmTestDefs0277";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
