open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2745Theory;
val () = new_theory "vfmTest2745";
val thyn = "vfmTestDefs2745";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
