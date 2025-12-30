Theory vfmTest1941[no_sig_docs]
Ancestors vfmTestDefs1941
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1941";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
