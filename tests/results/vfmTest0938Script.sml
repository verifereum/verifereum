open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0938Theory;
val () = new_theory "vfmTest0938";
val thyn = "vfmTestDefs0938";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
