open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2568Theory;
val () = new_theory "vfmTest2568";
val thyn = "vfmTestDefs2568";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
