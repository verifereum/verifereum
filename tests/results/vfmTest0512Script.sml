open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0512Theory;
val () = new_theory "vfmTest0512";
val thyn = "vfmTestDefs0512";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
