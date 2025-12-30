Theory vfmTest1255[no_sig_docs]
Ancestors vfmTestDefs1255
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1255";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
