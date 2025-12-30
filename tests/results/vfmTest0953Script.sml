Theory vfmTest0953[no_sig_docs]
Ancestors vfmTestDefs0953
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0953";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
