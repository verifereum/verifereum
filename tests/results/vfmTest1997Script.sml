Theory vfmTest1997[no_sig_docs]
Ancestors vfmTestDefs1997
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1997";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
