Theory vfmTest1991[no_sig_docs]
Ancestors vfmTestDefs1991
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1991";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
