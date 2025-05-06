open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0482Theory;
val () = new_theory "vfmTest0482";
val thyn = "vfmTestDefs0482";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
