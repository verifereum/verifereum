Theory vfmTest0554[no_sig_docs]
Ancestors vfmTestDefs0554
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0554";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
