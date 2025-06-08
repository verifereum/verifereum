open HolKernel wordsLib vfmTestResultLib vfmTestDefs0097Theory;
val () = new_theory "vfmTest0097";
val thyn = "vfmTestDefs0097";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
