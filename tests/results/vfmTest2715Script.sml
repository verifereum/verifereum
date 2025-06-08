open HolKernel wordsLib vfmTestResultLib vfmTestDefs2715Theory;
val () = new_theory "vfmTest2715";
val thyn = "vfmTestDefs2715";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
