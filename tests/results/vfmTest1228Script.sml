Theory vfmTest1228[no_sig_docs]
Ancestors vfmTestDefs1228
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1228";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
