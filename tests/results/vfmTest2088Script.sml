open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2088Theory;
val () = new_theory "vfmTest2088";
val thyn = "vfmTestDefs2088";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
