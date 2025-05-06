open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0568Theory;
val () = new_theory "vfmTest0568";
val thyn = "vfmTestDefs0568";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
