Theory vfmTest1770[no_sig_docs]
Ancestors vfmTestDefs1770
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1770";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
