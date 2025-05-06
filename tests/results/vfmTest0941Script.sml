open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0941Theory;
val () = new_theory "vfmTest0941";
val thyn = "vfmTestDefs0941";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
