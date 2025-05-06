open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1107Theory;
val () = new_theory "vfmTest1107";
val thyn = "vfmTestDefs1107";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
