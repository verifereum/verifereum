Theory vfmTest1609[no_sig_docs]
Ancestors vfmTestDefs1609
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1609";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
