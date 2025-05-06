open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1532Theory;
val () = new_theory "vfmTest1532";
val thyn = "vfmTestDefs1532";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
