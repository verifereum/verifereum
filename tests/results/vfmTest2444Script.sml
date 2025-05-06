open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2444Theory;
val () = new_theory "vfmTest2444";
val thyn = "vfmTestDefs2444";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
