open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0983Theory;
val () = new_theory "vfmTest0983";
val thyn = "vfmTestDefs0983";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
