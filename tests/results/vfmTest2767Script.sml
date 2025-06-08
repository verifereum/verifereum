open HolKernel wordsLib vfmTestResultLib vfmTestDefs2767Theory;
val () = new_theory "vfmTest2767";
val thyn = "vfmTestDefs2767";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
