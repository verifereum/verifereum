open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2897Theory;
val () = new_theory "vfmTest2897";
val thyn = "vfmTestDefs2897";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
