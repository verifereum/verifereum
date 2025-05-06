open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0470Theory;
val () = new_theory "vfmTest0470";
val thyn = "vfmTestDefs0470";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
