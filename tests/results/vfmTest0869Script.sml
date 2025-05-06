open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0869Theory;
val () = new_theory "vfmTest0869";
val thyn = "vfmTestDefs0869";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
