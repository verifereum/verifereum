Theory vfmTest1171[no_sig_docs]
Ancestors vfmTestDefs1171
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1171";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
