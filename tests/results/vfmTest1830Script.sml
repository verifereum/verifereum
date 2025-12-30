Theory vfmTest1830[no_sig_docs]
Ancestors vfmTestDefs1830
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1830";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
