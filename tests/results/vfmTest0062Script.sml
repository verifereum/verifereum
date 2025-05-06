open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0062Theory;
val () = new_theory "vfmTest0062";
val thyn = "vfmTestDefs0062";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
