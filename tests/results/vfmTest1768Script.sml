open HolKernel wordsLib vfmTestResultLib vfmTestDefs1768Theory;
val () = new_theory "vfmTest1768";
val thyn = "vfmTestDefs1768";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
