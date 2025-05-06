open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2500Theory;
val () = new_theory "vfmTest2500";
val thyn = "vfmTestDefs2500";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
