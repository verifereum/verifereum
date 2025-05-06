open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1132Theory;
val () = new_theory "vfmTest1132";
val thyn = "vfmTestDefs1132";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
