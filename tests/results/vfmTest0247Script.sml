open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0247Theory;
val () = new_theory "vfmTest0247";
val thyn = "vfmTestDefs0247";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
