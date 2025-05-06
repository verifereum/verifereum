open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2067Theory;
val () = new_theory "vfmTest2067";
val thyn = "vfmTestDefs2067";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
