open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0583Theory;
val () = new_theory "vfmTest0583";
val thyn = "vfmTestDefs0583";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
