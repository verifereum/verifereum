open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0168Theory;
val () = new_theory "vfmTest0168";
val thyn = "vfmTestDefs0168";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
