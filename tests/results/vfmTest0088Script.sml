Theory vfmTest0088[no_sig_docs]
Ancestors vfmTestDefs0088
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0088";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
