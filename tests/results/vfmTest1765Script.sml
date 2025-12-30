Theory vfmTest1765[no_sig_docs]
Ancestors vfmTestDefs1765
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1765";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
