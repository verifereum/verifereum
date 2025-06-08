open HolKernel wordsLib vfmTestResultLib vfmTestDefs1333Theory;
val () = new_theory "vfmTest1333";
val thyn = "vfmTestDefs1333";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
