open HolKernel wordsLib vfmTestResultLib vfmTestDefs0891Theory;
val () = new_theory "vfmTest0891";
val thyn = "vfmTestDefs0891";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
