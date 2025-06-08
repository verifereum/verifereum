open HolKernel wordsLib vfmTestResultLib vfmTestDefs2546Theory;
val () = new_theory "vfmTest2546";
val thyn = "vfmTestDefs2546";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
