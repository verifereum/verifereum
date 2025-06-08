open HolKernel wordsLib vfmTestResultLib vfmTestDefs0745Theory;
val () = new_theory "vfmTest0745";
val thyn = "vfmTestDefs0745";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
