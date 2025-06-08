open HolKernel wordsLib vfmTestResultLib vfmTestDefs1849Theory;
val () = new_theory "vfmTest1849";
val thyn = "vfmTestDefs1849";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
