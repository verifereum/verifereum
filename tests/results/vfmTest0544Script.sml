open HolKernel wordsLib vfmTestResultLib vfmTestDefs0544Theory;
val () = new_theory "vfmTest0544";
val thyn = "vfmTestDefs0544";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
