Theory vfmTest0167[no_sig_docs]
Ancestors vfmTestDefs0167
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0167";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
