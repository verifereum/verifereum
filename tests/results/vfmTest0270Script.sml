Theory vfmTest0270[no_sig_docs]
Ancestors vfmTestDefs0270
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0270";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
