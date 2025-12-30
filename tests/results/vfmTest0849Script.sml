Theory vfmTest0849[no_sig_docs]
Ancestors vfmTestDefs0849
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0849";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
