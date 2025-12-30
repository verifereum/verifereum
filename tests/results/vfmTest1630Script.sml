Theory vfmTest1630[no_sig_docs]
Ancestors vfmTestDefs1630
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1630";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
