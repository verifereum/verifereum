Theory vfmTest1156[no_sig_docs]
Ancestors vfmTestDefs1156
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1156";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
