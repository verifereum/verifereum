Theory vfmTest2408[no_sig_docs]
Ancestors vfmTestDefs2408
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2408";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
