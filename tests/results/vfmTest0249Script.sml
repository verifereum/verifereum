open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0249Theory;
val () = new_theory "vfmTest0249";
val thyn = "vfmTestDefs0249";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
