open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0029Theory;
val () = new_theory "vfmTest0029";
val thyn = "vfmTestDefs0029";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
