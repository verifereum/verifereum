Theory vfmTest1959[no_sig_docs]
Ancestors vfmTestDefs1959
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1959";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
