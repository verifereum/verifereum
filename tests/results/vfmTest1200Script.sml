open HolKernel wordsLib vfmTestResultLib vfmTestDefs1200Theory;
val () = new_theory "vfmTest1200";
val thyn = "vfmTestDefs1200";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
