open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0718Theory;
val () = new_theory "vfmTest0718";
val thyn = "vfmTestDefs0718";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
