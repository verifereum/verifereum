open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0184Theory;
val () = new_theory "vfmTest0184";
val thyn = "vfmTestDefs0184";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
