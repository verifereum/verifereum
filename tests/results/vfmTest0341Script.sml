Theory vfmTest0341[no_sig_docs]
Ancestors vfmTestDefs0341
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0341";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
