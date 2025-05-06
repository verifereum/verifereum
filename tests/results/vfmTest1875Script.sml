open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1875Theory;
val () = new_theory "vfmTest1875";
val thyn = "vfmTestDefs1875";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
