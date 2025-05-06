open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2821Theory;
val () = new_theory "vfmTest2821";
val thyn = "vfmTestDefs2821";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
