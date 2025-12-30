Theory vfmTest0760[no_sig_docs]
Ancestors vfmTestDefs0760
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0760";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
