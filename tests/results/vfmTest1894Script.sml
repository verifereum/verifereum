Theory vfmTest1894[no_sig_docs]
Ancestors vfmTestDefs1894
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1894";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
