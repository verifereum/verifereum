Theory vfmTest1290[no_sig_docs]
Ancestors vfmTestDefs1290
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1290";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
