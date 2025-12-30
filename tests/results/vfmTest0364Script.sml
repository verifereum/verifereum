Theory vfmTest0364[no_sig_docs]
Ancestors vfmTestDefs0364
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0364";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
