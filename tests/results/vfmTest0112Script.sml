Theory vfmTest0112[no_sig_docs]
Ancestors vfmTestDefs0112
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0112";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
