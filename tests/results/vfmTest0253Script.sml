open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0253Theory;
val () = new_theory "vfmTest0253";
val thyn = "vfmTestDefs0253";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
