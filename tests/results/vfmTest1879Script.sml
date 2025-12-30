Theory vfmTest1879[no_sig_docs]
Ancestors vfmTestDefs1879
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1879";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
