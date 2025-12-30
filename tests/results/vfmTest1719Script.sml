Theory vfmTest1719[no_sig_docs]
Ancestors vfmTestDefs1719
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1719";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
