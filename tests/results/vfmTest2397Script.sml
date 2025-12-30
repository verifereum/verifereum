Theory vfmTest2397[no_sig_docs]
Ancestors vfmTestDefs2397
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2397";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
