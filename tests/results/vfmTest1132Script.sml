Theory vfmTest1132[no_sig_docs]
Ancestors vfmTestDefs1132
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1132";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
