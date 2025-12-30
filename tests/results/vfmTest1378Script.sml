Theory vfmTest1378[no_sig_docs]
Ancestors vfmTestDefs1378
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1378";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
