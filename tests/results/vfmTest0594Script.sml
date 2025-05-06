open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0594Theory;
val () = new_theory "vfmTest0594";
val thyn = "vfmTestDefs0594";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
