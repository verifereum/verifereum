open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0586Theory;
val () = new_theory "vfmTest0586";
val thyn = "vfmTestDefs0586";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
