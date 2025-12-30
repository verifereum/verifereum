Theory vfmTest1340[no_sig_docs]
Ancestors vfmTestDefs1340
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1340";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
