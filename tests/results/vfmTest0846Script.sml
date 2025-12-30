Theory vfmTest0846[no_sig_docs]
Ancestors vfmTestDefs0846
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0846";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
