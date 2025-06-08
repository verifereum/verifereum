open HolKernel wordsLib vfmTestResultLib vfmTestDefs1607Theory;
val () = new_theory "vfmTest1607";
val thyn = "vfmTestDefs1607";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
