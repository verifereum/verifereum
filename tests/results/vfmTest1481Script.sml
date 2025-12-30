Theory vfmTest1481[no_sig_docs]
Ancestors vfmTestDefs1481
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1481";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
