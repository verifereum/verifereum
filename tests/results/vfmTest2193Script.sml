open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2193Theory;
val () = new_theory "vfmTest2193";
val thyn = "vfmTestDefs2193";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
