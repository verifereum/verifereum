Theory vfmTest1239[no_sig_docs]
Ancestors vfmTestDefs1239
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1239";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
