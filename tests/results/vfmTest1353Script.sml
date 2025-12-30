Theory vfmTest1353[no_sig_docs]
Ancestors vfmTestDefs1353
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1353";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
