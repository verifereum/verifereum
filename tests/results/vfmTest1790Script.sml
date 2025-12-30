Theory vfmTest1790[no_sig_docs]
Ancestors vfmTestDefs1790
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1790";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
