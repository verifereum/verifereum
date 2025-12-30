Theory vfmTest0483[no_sig_docs]
Ancestors vfmTestDefs0483
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0483";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
