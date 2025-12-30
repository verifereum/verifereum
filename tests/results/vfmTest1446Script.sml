Theory vfmTest1446[no_sig_docs]
Ancestors vfmTestDefs1446
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1446";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
