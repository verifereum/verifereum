Theory vfmTest0963[no_sig_docs]
Ancestors vfmTestDefs0963
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0963";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
