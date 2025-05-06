open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0423Theory;
val () = new_theory "vfmTest0423";
val thyn = "vfmTestDefs0423";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
