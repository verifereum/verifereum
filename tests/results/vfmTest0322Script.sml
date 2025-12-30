Theory vfmTest0322[no_sig_docs]
Ancestors vfmTestDefs0322
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0322";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
