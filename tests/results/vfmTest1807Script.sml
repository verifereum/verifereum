open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1807Theory;
val () = new_theory "vfmTest1807";
val thyn = "vfmTestDefs1807";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
