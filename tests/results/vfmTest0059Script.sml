open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0059Theory;
val () = new_theory "vfmTest0059";
val thyn = "vfmTestDefs0059";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
