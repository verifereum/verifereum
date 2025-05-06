open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0330Theory;
val () = new_theory "vfmTest0330";
val thyn = "vfmTestDefs0330";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
