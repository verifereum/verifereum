Theory vfmTest0799[no_sig_docs]
Ancestors vfmTestDefs0799
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0799";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
