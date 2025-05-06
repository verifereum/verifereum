open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0624Theory;
val () = new_theory "vfmTest0624";
val thyn = "vfmTestDefs0624";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
