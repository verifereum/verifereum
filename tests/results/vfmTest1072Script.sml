Theory vfmTest1072[no_sig_docs]
Ancestors vfmTestDefs1072
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1072";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
