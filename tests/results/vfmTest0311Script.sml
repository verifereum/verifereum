open HolKernel wordsLib vfmTestResultLib vfmTestDefs0311Theory;
val () = new_theory "vfmTest0311";
val thyn = "vfmTestDefs0311";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
