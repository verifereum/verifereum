Theory vfmTest1060[no_sig_docs]
Ancestors vfmTestDefs1060
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1060";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
