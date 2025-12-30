Theory vfmTest0814[no_sig_docs]
Ancestors vfmTestDefs0814
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0814";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
