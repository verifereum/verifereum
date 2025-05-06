open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0629Theory;
val () = new_theory "vfmTest0629";
val thyn = "vfmTestDefs0629";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
