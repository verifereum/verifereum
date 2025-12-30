Theory vfmTest1356[no_sig_docs]
Ancestors vfmTestDefs1356
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1356";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
