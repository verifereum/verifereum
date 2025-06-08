open HolKernel wordsLib vfmTestResultLib vfmTestDefs1913Theory;
val () = new_theory "vfmTest1913";
val thyn = "vfmTestDefs1913";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
