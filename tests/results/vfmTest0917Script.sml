open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0917Theory;
val () = new_theory "vfmTest0917";
val thyn = "vfmTestDefs0917";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
