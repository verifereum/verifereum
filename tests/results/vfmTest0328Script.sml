open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0328Theory;
val () = new_theory "vfmTest0328";
val thyn = "vfmTestDefs0328";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
