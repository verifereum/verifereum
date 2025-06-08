open HolKernel wordsLib vfmTestResultLib vfmTestDefs2066Theory;
val () = new_theory "vfmTest2066";
val thyn = "vfmTestDefs2066";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
