Theory vfmTest2379[no_sig_docs]
Ancestors vfmTestDefs2379
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2379";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
