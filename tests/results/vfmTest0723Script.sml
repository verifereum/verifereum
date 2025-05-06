open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0723Theory;
val () = new_theory "vfmTest0723";
val thyn = "vfmTestDefs0723";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
