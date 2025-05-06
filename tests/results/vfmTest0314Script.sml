open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0314Theory;
val () = new_theory "vfmTest0314";
val thyn = "vfmTestDefs0314";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
