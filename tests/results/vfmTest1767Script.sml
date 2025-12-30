Theory vfmTest1767[no_sig_docs]
Ancestors vfmTestDefs1767
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1767";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
