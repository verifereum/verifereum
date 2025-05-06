open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0288Theory;
val () = new_theory "vfmTest0288";
val thyn = "vfmTestDefs0288";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
