Theory vfmTest0756[no_sig_docs]
Ancestors vfmTestDefs0756
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0756";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
