open HolKernel wordsLib vfmTestResultLib vfmTestDefs2497Theory;
val () = new_theory "vfmTest2497";
val thyn = "vfmTestDefs2497";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
