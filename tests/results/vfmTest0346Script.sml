open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0346Theory;
val () = new_theory "vfmTest0346";
val thyn = "vfmTestDefs0346";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
