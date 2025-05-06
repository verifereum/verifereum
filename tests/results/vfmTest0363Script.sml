open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0363Theory;
val () = new_theory "vfmTest0363";
val thyn = "vfmTestDefs0363";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
