open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0472Theory;
val () = new_theory "vfmTest0472";
val thyn = "vfmTestDefs0472";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
