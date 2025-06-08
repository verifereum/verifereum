open HolKernel wordsLib vfmTestResultLib vfmTestDefs0940Theory;
val () = new_theory "vfmTest0940";
val thyn = "vfmTestDefs0940";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
