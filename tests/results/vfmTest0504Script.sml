open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0504Theory;
val () = new_theory "vfmTest0504";
val thyn = "vfmTestDefs0504";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
