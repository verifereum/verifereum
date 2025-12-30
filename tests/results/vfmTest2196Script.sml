Theory vfmTest2196[no_sig_docs]
Ancestors vfmTestDefs2196
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2196";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
