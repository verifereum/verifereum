open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0642Theory;
val () = new_theory "vfmTest0642";
val thyn = "vfmTestDefs0642";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
