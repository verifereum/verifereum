Theory vfmTest1057[no_sig_docs]
Ancestors vfmTestDefs1057
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1057";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
