open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0806Theory;
val () = new_theory "vfmTest0806";
val thyn = "vfmTestDefs0806";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
