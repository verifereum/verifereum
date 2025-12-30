Theory vfmTest2527[no_sig_docs]
Ancestors vfmTestDefs2527
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2527";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
