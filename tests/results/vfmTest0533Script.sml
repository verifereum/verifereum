open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0533Theory;
val () = new_theory "vfmTest0533";
val thyn = "vfmTestDefs0533";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
