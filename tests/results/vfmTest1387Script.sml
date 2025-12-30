Theory vfmTest1387[no_sig_docs]
Ancestors vfmTestDefs1387
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1387";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
