Theory vfmTest1076[no_sig_docs]
Ancestors vfmTestDefs1076
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1076";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
