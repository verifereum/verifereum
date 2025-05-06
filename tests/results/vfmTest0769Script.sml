open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0769Theory;
val () = new_theory "vfmTest0769";
val thyn = "vfmTestDefs0769";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
