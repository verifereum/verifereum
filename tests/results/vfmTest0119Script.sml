Theory vfmTest0119[no_sig_docs]
Ancestors vfmTestDefs0119
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0119";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
