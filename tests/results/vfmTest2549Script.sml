Theory vfmTest2549[no_sig_docs]
Ancestors vfmTestDefs2549
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2549";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
