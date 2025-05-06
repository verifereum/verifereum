open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0614Theory;
val () = new_theory "vfmTest0614";
val thyn = "vfmTestDefs0614";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
