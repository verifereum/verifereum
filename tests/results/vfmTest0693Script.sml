open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0693Theory;
val () = new_theory "vfmTest0693";
val thyn = "vfmTestDefs0693";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
