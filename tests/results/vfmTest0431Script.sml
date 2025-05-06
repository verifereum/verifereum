open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0431Theory;
val () = new_theory "vfmTest0431";
val thyn = "vfmTestDefs0431";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
