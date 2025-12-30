Theory vfmTest1845[no_sig_docs]
Ancestors vfmTestDefs1845
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1845";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
