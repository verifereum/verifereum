open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1397Theory;
val () = new_theory "vfmTest1397";
val thyn = "vfmTestDefs1397";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
