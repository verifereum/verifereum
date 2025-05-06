open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0534Theory;
val () = new_theory "vfmTest0534";
val thyn = "vfmTestDefs0534";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
