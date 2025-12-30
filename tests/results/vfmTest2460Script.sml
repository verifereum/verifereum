Theory vfmTest2460[no_sig_docs]
Ancestors vfmTestDefs2460
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2460";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
