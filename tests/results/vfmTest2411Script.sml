Theory vfmTest2411[no_sig_docs]
Ancestors vfmTestDefs2411
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2411";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
