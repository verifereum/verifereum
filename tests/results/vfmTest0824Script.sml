open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0824Theory;
val () = new_theory "vfmTest0824";
val thyn = "vfmTestDefs0824";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
