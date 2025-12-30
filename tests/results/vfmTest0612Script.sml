Theory vfmTest0612[no_sig_docs]
Ancestors vfmTestDefs0612
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0612";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
