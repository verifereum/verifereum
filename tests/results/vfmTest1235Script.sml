Theory vfmTest1235[no_sig_docs]
Ancestors vfmTestDefs1235
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1235";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
