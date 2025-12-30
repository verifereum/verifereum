Theory vfmTest2287[no_sig_docs]
Ancestors vfmTestDefs2287
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2287";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
