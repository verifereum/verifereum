open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0095Theory;
val () = new_theory "vfmTest0095";
val thyn = "vfmTestDefs0095";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
