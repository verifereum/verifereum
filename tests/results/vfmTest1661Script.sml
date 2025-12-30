Theory vfmTest1661[no_sig_docs]
Ancestors vfmTestDefs1661
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1661";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
