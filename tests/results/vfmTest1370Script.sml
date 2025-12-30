Theory vfmTest1370[no_sig_docs]
Ancestors vfmTestDefs1370
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1370";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
