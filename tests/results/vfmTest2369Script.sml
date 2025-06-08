open HolKernel wordsLib vfmTestResultLib vfmTestDefs2369Theory;
val () = new_theory "vfmTest2369";
val thyn = "vfmTestDefs2369";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
