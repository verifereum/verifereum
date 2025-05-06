open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1822Theory;
val () = new_theory "vfmTest1822";
val thyn = "vfmTestDefs1822";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
