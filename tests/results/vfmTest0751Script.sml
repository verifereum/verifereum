open HolKernel wordsLib vfmTestResultLib vfmTestDefs0751Theory;
val () = new_theory "vfmTest0751";
val thyn = "vfmTestDefs0751";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
