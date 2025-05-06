open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0164Theory;
val () = new_theory "vfmTest0164";
val thyn = "vfmTestDefs0164";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
