open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1463Theory;
val () = new_theory "vfmTest1463";
val thyn = "vfmTestDefs1463";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
