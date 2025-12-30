Theory vfmTest1472[no_sig_docs]
Ancestors vfmTestDefs1472
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1472";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
