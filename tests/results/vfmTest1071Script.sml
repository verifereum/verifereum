Theory vfmTest1071[no_sig_docs]
Ancestors vfmTestDefs1071
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1071";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
