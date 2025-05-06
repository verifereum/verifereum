open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0899Theory;
val () = new_theory "vfmTest0899";
val thyn = "vfmTestDefs0899";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
