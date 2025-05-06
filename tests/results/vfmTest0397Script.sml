open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0397Theory;
val () = new_theory "vfmTest0397";
val thyn = "vfmTestDefs0397";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
