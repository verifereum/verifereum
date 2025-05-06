open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0638Theory;
val () = new_theory "vfmTest0638";
val thyn = "vfmTestDefs0638";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
