open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0734Theory;
val () = new_theory "vfmTest0734";
val thyn = "vfmTestDefs0734";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
