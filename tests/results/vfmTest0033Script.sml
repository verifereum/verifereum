Theory vfmTest0033[no_sig_docs]
Ancestors vfmTestDefs0033
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0033";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
