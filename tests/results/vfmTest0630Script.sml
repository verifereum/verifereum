open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0630Theory;
val () = new_theory "vfmTest0630";
val thyn = "vfmTestDefs0630";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
