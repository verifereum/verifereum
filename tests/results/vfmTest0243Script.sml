open HolKernel wordsLib vfmTestResultLib vfmTestDefs0243Theory;
val () = new_theory "vfmTest0243";
val thyn = "vfmTestDefs0243";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
