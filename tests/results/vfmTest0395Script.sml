open HolKernel wordsLib vfmTestResultLib vfmTestDefs0395Theory;
val () = new_theory "vfmTest0395";
val thyn = "vfmTestDefs0395";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
