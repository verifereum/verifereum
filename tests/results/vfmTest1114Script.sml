open HolKernel wordsLib vfmTestResultLib vfmTestDefs1114Theory;
val () = new_theory "vfmTest1114";
val thyn = "vfmTestDefs1114";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
