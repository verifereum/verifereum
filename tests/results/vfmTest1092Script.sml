Theory vfmTest1092[no_sig_docs]
Ancestors vfmTestDefs1092
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1092";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
