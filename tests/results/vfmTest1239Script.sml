open HolKernel wordsLib vfmTestResultLib vfmTestDefs1239Theory;
val () = new_theory "vfmTest1239";
val thyn = "vfmTestDefs1239";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
