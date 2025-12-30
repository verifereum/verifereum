Theory vfmTest2312[no_sig_docs]
Ancestors vfmTestDefs2312
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2312";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
