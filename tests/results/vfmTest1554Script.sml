Theory vfmTest1554[no_sig_docs]
Ancestors vfmTestDefs1554
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1554";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
