Theory vfmTest2598[no_sig_docs]
Ancestors vfmTestDefs2598
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2598";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
