open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0539Theory;
val () = new_theory "vfmTest0539";
val thyn = "vfmTestDefs0539";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
