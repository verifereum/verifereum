open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0079Theory;
val () = new_theory "vfmTest0079";
val thyn = "vfmTestDefs0079";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
