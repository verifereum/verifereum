Theory vfmTest0680[no_sig_docs]
Ancestors vfmTestDefs0680
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0680";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
