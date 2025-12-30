Theory vfmTest1527[no_sig_docs]
Ancestors vfmTestDefs1527
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1527";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
