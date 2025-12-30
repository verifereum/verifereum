Theory vfmTest1529[no_sig_docs]
Ancestors vfmTestDefs1529
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1529";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
