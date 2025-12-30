Theory vfmTest1716[no_sig_docs]
Ancestors vfmTestDefs1716
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1716";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
