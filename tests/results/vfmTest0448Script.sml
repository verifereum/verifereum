open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0448Theory;
val () = new_theory "vfmTest0448";
val thyn = "vfmTestDefs0448";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
