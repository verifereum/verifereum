Theory vfmTest1003[no_sig_docs]
Ancestors vfmTestDefs1003
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1003";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
