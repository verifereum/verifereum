open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0687Theory;
val () = new_theory "vfmTest0687";
val thyn = "vfmTestDefs0687";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
