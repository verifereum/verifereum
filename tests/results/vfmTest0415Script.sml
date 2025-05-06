open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0415Theory;
val () = new_theory "vfmTest0415";
val thyn = "vfmTestDefs0415";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
