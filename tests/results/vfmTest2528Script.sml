open HolKernel wordsLib vfmTestResultLib vfmTestDefs2528Theory;
val () = new_theory "vfmTest2528";
val thyn = "vfmTestDefs2528";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
