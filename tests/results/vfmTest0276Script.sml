open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0276Theory;
val () = new_theory "vfmTest0276";
val thyn = "vfmTestDefs0276";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
