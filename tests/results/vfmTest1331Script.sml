Theory vfmTest1331[no_sig_docs]
Ancestors vfmTestDefs1331
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1331";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
