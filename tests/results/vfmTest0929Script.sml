open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0929Theory;
val () = new_theory "vfmTest0929";
val thyn = "vfmTestDefs0929";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
