Theory vfmTest1853[no_sig_docs]
Ancestors vfmTestDefs1853
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1853";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
