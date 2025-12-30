Theory vfmTest0811[no_sig_docs]
Ancestors vfmTestDefs0811
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0811";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
