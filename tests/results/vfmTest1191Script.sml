open HolKernel wordsLib vfmTestResultLib vfmTestDefs1191Theory;
val () = new_theory "vfmTest1191";
val thyn = "vfmTestDefs1191";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
