open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0150Theory;
val () = new_theory "vfmTest0150";
val thyn = "vfmTestDefs0150";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
