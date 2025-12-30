Theory vfmTest2739[no_sig_docs]
Ancestors vfmTestDefs2739
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2739";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
