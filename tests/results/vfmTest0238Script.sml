Theory vfmTest0238[no_sig_docs]
Ancestors vfmTestDefs0238
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0238";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
