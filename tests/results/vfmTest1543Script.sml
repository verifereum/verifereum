open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1543Theory;
val () = new_theory "vfmTest1543";
val thyn = "vfmTestDefs1543";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
