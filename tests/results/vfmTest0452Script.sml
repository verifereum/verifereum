open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0452Theory;
val () = new_theory "vfmTest0452";
val thyn = "vfmTestDefs0452";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
