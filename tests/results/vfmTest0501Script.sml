open HolKernel wordsLib vfmTestResultLib vfmTestDefs0501Theory;
val () = new_theory "vfmTest0501";
val thyn = "vfmTestDefs0501";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
