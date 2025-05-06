open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0428Theory;
val () = new_theory "vfmTest0428";
val thyn = "vfmTestDefs0428";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
