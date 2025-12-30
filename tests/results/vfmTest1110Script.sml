Theory vfmTest1110[no_sig_docs]
Ancestors vfmTestDefs1110
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1110";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
