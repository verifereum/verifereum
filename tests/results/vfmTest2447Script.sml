Theory vfmTest2447[no_sig_docs]
Ancestors vfmTestDefs2447
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2447";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
