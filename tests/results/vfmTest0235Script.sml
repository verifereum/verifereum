open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0235Theory;
val () = new_theory "vfmTest0235";
val thyn = "vfmTestDefs0235";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
