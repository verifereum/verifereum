open HolKernel wordsLib vfmTestResultLib vfmTestDefs0240Theory;
val () = new_theory "vfmTest0240";
val thyn = "vfmTestDefs0240";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
