open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0248Theory;
val () = new_theory "vfmTest0248";
val thyn = "vfmTestDefs0248";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
