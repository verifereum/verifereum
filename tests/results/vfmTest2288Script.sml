open HolKernel wordsLib vfmTestResultLib vfmTestDefs2288Theory;
val () = new_theory "vfmTest2288";
val thyn = "vfmTestDefs2288";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
