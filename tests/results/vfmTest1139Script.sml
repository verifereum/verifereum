Theory vfmTest1139[no_sig_docs]
Ancestors vfmTestDefs1139
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1139";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
