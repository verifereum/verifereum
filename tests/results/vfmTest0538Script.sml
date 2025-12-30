Theory vfmTest0538[no_sig_docs]
Ancestors vfmTestDefs0538
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0538";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
