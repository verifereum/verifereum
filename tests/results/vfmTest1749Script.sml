Theory vfmTest1749[no_sig_docs]
Ancestors vfmTestDefs1749
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1749";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
