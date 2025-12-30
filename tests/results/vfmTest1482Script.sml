Theory vfmTest1482[no_sig_docs]
Ancestors vfmTestDefs1482
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1482";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
