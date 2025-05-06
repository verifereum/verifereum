open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0664Theory;
val () = new_theory "vfmTest0664";
val thyn = "vfmTestDefs0664";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
