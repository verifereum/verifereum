open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0616Theory;
val () = new_theory "vfmTest0616";
val thyn = "vfmTestDefs0616";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
