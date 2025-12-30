Theory vfmTest0787[no_sig_docs]
Ancestors vfmTestDefs0787
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0787";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
