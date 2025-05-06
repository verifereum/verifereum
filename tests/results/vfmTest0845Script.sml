open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0845Theory;
val () = new_theory "vfmTest0845";
val thyn = "vfmTestDefs0845";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
