Theory vfmTest1064[no_sig_docs]
Ancestors vfmTestDefs1064
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1064";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
