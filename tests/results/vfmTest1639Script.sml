open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1639Theory;
val () = new_theory "vfmTest1639";
val thyn = "vfmTestDefs1639";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
