open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0364Theory;
val () = new_theory "vfmTest0364";
val thyn = "vfmTestDefs0364";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
