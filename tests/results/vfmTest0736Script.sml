open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0736Theory;
val () = new_theory "vfmTest0736";
val thyn = "vfmTestDefs0736";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
