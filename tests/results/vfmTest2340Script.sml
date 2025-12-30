Theory vfmTest2340[no_sig_docs]
Ancestors vfmTestDefs2340
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2340";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
