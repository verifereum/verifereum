open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1868Theory;
val () = new_theory "vfmTest1868";
val thyn = "vfmTestDefs1868";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
