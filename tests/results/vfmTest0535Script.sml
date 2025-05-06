open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0535Theory;
val () = new_theory "vfmTest0535";
val thyn = "vfmTestDefs0535";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
