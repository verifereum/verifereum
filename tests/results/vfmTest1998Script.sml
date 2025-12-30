Theory vfmTest1998[no_sig_docs]
Ancestors vfmTestDefs1998
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1998";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
