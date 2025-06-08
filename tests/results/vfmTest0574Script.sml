open HolKernel wordsLib vfmTestResultLib vfmTestDefs0574Theory;
val () = new_theory "vfmTest0574";
val thyn = "vfmTestDefs0574";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
