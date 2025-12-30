Theory vfmTest1001[no_sig_docs]
Ancestors vfmTestDefs1001
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1001";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
