Theory vfmTest1078[no_sig_docs]
Ancestors vfmTestDefs1078
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1078";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
