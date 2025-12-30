Theory vfmTest2459[no_sig_docs]
Ancestors vfmTestDefs2459
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2459";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
