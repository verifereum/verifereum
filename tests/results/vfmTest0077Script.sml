open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0077Theory;
val () = new_theory "vfmTest0077";
val thyn = "vfmTestDefs0077";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
