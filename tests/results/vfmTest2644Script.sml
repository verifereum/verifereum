open HolKernel wordsLib vfmTestResultLib vfmTestDefs2644Theory;
val () = new_theory "vfmTest2644";
val thyn = "vfmTestDefs2644";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
