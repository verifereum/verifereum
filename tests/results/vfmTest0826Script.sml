open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0826Theory;
val () = new_theory "vfmTest0826";
val thyn = "vfmTestDefs0826";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
