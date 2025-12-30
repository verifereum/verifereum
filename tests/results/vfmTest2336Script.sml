Theory vfmTest2336[no_sig_docs]
Ancestors vfmTestDefs2336
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2336";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
