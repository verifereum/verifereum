Theory vfmTest2653[no_sig_docs]
Ancestors vfmTestDefs2653
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2653";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
