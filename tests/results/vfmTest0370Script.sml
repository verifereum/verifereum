Theory vfmTest0370[no_sig_docs]
Ancestors vfmTestDefs0370
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0370";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
