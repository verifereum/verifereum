open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0508Theory;
val () = new_theory "vfmTest0508";
val thyn = "vfmTestDefs0508";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
