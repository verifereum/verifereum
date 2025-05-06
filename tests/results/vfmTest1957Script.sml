open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1957Theory;
val () = new_theory "vfmTest1957";
val thyn = "vfmTestDefs1957";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
