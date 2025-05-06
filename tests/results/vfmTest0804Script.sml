open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0804Theory;
val () = new_theory "vfmTest0804";
val thyn = "vfmTestDefs0804";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
