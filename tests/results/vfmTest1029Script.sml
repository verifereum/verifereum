Theory vfmTest1029[no_sig_docs]
Ancestors vfmTestDefs1029
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1029";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
