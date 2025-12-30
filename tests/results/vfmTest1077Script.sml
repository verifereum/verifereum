Theory vfmTest1077[no_sig_docs]
Ancestors vfmTestDefs1077
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1077";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
