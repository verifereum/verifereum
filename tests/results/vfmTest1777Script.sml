Theory vfmTest1777[no_sig_docs]
Ancestors vfmTestDefs1777
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1777";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
