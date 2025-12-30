Theory vfmTest1688[no_sig_docs]
Ancestors vfmTestDefs1688
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1688";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
