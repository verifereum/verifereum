open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2875Theory;
val () = new_theory "vfmTest2875";
val thyn = "vfmTestDefs2875";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
