Theory vfmTest0527[no_sig_docs]
Ancestors vfmTestDefs0527
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0527";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
