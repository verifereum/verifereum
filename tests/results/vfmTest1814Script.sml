Theory vfmTest1814[no_sig_docs]
Ancestors vfmTestDefs1814
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1814";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
