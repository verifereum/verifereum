Theory vfmTest1180[no_sig_docs]
Ancestors vfmTestDefs1180
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1180";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
