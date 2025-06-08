open HolKernel wordsLib vfmTestResultLib vfmTestDefs2001Theory;
val () = new_theory "vfmTest2001";
val thyn = "vfmTestDefs2001";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
