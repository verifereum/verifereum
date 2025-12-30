Theory vfmTest1417[no_sig_docs]
Ancestors vfmTestDefs1417
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1417";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
