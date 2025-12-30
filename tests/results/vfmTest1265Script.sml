Theory vfmTest1265[no_sig_docs]
Ancestors vfmTestDefs1265
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1265";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
