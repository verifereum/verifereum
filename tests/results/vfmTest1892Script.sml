Theory vfmTest1892[no_sig_docs]
Ancestors vfmTestDefs1892
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1892";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
