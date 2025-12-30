Theory vfmTest0363[no_sig_docs]
Ancestors vfmTestDefs0363
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0363";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
