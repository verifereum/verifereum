Theory vfmTest0045[no_sig_docs]
Ancestors vfmTestDefs0045
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0045";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
