Theory vfmTest2358[no_sig_docs]
Ancestors vfmTestDefs2358
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2358";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
