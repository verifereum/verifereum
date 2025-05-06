open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2820Theory;
val () = new_theory "vfmTest2820";
val thyn = "vfmTestDefs2820";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
