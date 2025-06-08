open HolKernel wordsLib vfmTestResultLib vfmTestDefs1064Theory;
val () = new_theory "vfmTest1064";
val thyn = "vfmTestDefs1064";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
