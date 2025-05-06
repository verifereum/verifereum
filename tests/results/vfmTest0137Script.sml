open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0137Theory;
val () = new_theory "vfmTest0137";
val thyn = "vfmTestDefs0137";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
