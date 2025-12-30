Theory vfmTest2395[no_sig_docs]
Ancestors vfmTestDefs2395
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2395";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
