Theory vfmTest2454[no_sig_docs]
Ancestors vfmTestDefs2454
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2454";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
