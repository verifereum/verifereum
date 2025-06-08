open HolKernel wordsLib vfmTestResultLib vfmTestDefs2349Theory;
val () = new_theory "vfmTest2349";
val thyn = "vfmTestDefs2349";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
