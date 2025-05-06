open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1425Theory;
val () = new_theory "vfmTest1425";
val thyn = "vfmTestDefs1425";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
