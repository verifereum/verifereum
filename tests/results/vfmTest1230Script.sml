Theory vfmTest1230[no_sig_docs]
Ancestors vfmTestDefs1230
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1230";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
