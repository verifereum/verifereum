open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0626Theory;
val () = new_theory "vfmTest0626";
val thyn = "vfmTestDefs0626";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
