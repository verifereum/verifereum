open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2221Theory;
val () = new_theory "vfmTest2221";
val thyn = "vfmTestDefs2221";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
