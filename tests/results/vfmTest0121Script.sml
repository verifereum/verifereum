open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0121Theory;
val () = new_theory "vfmTest0121";
val thyn = "vfmTestDefs0121";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
