open HolKernel wordsLib vfmTestResultLib vfmTestDefs1639Theory;
val () = new_theory "vfmTest1639";
val thyn = "vfmTestDefs1639";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
