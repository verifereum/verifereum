Theory vfmTest1610[no_sig_docs]
Ancestors vfmTestDefs1610
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1610";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
