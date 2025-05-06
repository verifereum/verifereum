open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1290Theory;
val () = new_theory "vfmTest1290";
val thyn = "vfmTestDefs1290";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
