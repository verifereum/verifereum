open HolKernel wordsLib vfmTestResultLib vfmTestDefs0735Theory;
val () = new_theory "vfmTest0735";
val thyn = "vfmTestDefs0735";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
