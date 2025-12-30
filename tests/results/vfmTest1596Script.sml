Theory vfmTest1596[no_sig_docs]
Ancestors vfmTestDefs1596
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1596";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
