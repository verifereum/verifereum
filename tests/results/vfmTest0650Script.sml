Theory vfmTest0650[no_sig_docs]
Ancestors vfmTestDefs0650
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0650";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
