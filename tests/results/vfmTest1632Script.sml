Theory vfmTest1632[no_sig_docs]
Ancestors vfmTestDefs1632
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1632";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
