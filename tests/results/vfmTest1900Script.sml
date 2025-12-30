Theory vfmTest1900[no_sig_docs]
Ancestors vfmTestDefs1900
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1900";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
