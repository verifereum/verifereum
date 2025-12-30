Theory vfmTest1513[no_sig_docs]
Ancestors vfmTestDefs1513
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1513";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
