Theory vfmTest1112[no_sig_docs]
Ancestors vfmTestDefs1112
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1112";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
