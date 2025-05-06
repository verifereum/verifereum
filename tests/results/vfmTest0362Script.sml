open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0362Theory;
val () = new_theory "vfmTest0362";
val thyn = "vfmTestDefs0362";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
