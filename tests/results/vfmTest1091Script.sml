Theory vfmTest1091[no_sig_docs]
Ancestors vfmTestDefs1091
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1091";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
