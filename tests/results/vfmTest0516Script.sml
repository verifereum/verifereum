open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0516Theory;
val () = new_theory "vfmTest0516";
val thyn = "vfmTestDefs0516";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
