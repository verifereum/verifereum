Theory vfmTest0943[no_sig_docs]
Ancestors vfmTestDefs0943
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0943";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
