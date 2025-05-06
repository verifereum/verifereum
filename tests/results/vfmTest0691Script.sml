open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0691Theory;
val () = new_theory "vfmTest0691";
val thyn = "vfmTestDefs0691";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
