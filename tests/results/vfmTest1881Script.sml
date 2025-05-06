open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1881Theory;
val () = new_theory "vfmTest1881";
val thyn = "vfmTestDefs1881";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
