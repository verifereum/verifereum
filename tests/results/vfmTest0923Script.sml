Theory vfmTest0923[no_sig_docs]
Ancestors vfmTestDefs0923
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0923";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
