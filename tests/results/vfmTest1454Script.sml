open HolKernel wordsLib vfmTestResultLib vfmTestDefs1454Theory;
val () = new_theory "vfmTest1454";
val thyn = "vfmTestDefs1454";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
