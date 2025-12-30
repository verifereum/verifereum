Theory vfmTest1829[no_sig_docs]
Ancestors vfmTestDefs1829
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1829";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
