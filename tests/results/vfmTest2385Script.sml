Theory vfmTest2385[no_sig_docs]
Ancestors vfmTestDefs2385
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2385";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
