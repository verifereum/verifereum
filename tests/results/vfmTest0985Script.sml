open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0985Theory;
val () = new_theory "vfmTest0985";
val thyn = "vfmTestDefs0985";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
