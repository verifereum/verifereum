open HolKernel wordsLib vfmTestResultLib vfmTestDefs1340Theory;
val () = new_theory "vfmTest1340";
val thyn = "vfmTestDefs1340";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
