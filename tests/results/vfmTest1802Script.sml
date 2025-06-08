open HolKernel wordsLib vfmTestResultLib vfmTestDefs1802Theory;
val () = new_theory "vfmTest1802";
val thyn = "vfmTestDefs1802";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
