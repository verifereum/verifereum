Theory vfmTest1406[no_sig_docs]
Ancestors vfmTestDefs1406
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1406";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
