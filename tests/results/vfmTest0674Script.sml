open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0674Theory;
val () = new_theory "vfmTest0674";
val thyn = "vfmTestDefs0674";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
