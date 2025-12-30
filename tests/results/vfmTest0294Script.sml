Theory vfmTest0294[no_sig_docs]
Ancestors vfmTestDefs0294
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0294";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
