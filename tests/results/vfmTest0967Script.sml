open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0967Theory;
val () = new_theory "vfmTest0967";
val thyn = "vfmTestDefs0967";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
