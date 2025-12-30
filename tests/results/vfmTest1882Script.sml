Theory vfmTest1882[no_sig_docs]
Ancestors vfmTestDefs1882
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1882";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
