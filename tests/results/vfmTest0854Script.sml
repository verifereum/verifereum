Theory vfmTest0854[no_sig_docs]
Ancestors vfmTestDefs0854
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0854";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
