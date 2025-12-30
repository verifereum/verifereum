Theory vfmTest1086[no_sig_docs]
Ancestors vfmTestDefs1086
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1086";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
