open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0088Theory;
val () = new_theory "vfmTest0088";
val thyn = "vfmTestDefs0088";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
