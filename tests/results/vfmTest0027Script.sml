open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0027Theory;
val () = new_theory "vfmTest0027";
val thyn = "vfmTestDefs0027";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
