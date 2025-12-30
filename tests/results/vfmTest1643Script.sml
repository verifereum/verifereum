Theory vfmTest1643[no_sig_docs]
Ancestors vfmTestDefs1643
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1643";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
