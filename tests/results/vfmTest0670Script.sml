open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0670Theory;
val () = new_theory "vfmTest0670";
val thyn = "vfmTestDefs0670";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
