Theory vfmTest1599[no_sig_docs]
Ancestors vfmTestDefs1599
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1599";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
