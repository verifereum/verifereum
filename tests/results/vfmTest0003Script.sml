Theory vfmTest0003[no_sig_docs]
Ancestors vfmTestDefs0003
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0003";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
