Theory vfmTest2499[no_sig_docs]
Ancestors vfmTestDefs2499
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2499";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
