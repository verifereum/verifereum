Theory vfmTest1858[no_sig_docs]
Ancestors vfmTestDefs1858
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1858";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
