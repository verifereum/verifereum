Theory vfmTest2404[no_sig_docs]
Ancestors vfmTestDefs2404
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2404";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
