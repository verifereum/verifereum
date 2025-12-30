Theory vfmTest1074[no_sig_docs]
Ancestors vfmTestDefs1074
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1074";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
