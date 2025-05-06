open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0243Theory;
val () = new_theory "vfmTest0243";
val thyn = "vfmTestDefs0243";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
