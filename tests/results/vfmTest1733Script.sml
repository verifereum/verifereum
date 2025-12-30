Theory vfmTest1733[no_sig_docs]
Ancestors vfmTestDefs1733
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1733";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
