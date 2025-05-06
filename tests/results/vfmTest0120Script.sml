open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0120Theory;
val () = new_theory "vfmTest0120";
val thyn = "vfmTestDefs0120";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
