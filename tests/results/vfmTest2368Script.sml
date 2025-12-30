Theory vfmTest2368[no_sig_docs]
Ancestors vfmTestDefs2368
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2368";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
