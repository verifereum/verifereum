open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0478Theory;
val () = new_theory "vfmTest0478";
val thyn = "vfmTestDefs0478";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
