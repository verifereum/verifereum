Theory vfmTest1371[no_sig_docs]
Ancestors vfmTestDefs1371
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1371";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
