Theory vfmTest0083[no_sig_docs]
Ancestors vfmTestDefs0083
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0083";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
