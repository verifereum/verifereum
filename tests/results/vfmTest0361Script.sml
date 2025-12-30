Theory vfmTest0361[no_sig_docs]
Ancestors vfmTestDefs0361
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0361";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
