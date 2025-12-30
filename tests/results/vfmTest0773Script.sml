Theory vfmTest0773[no_sig_docs]
Ancestors vfmTestDefs0773
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0773";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
