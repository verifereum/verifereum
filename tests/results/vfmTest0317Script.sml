open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0317Theory;
val () = new_theory "vfmTest0317";
val thyn = "vfmTestDefs0317";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
