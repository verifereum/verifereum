open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2436Theory;
val () = new_theory "vfmTest2436";
val thyn = "vfmTestDefs2436";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
