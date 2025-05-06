open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0543Theory;
val () = new_theory "vfmTest0543";
val thyn = "vfmTestDefs0543";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
