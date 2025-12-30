Theory vfmTest0798[no_sig_docs]
Ancestors vfmTestDefs0798
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0798";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
