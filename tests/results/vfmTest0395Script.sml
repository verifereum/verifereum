open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0395Theory;
val () = new_theory "vfmTest0395";
val thyn = "vfmTestDefs0395";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
