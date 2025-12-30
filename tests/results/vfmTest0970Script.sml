Theory vfmTest0970[no_sig_docs]
Ancestors vfmTestDefs0970
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0970";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
