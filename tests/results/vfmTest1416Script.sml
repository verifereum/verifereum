Theory vfmTest1416[no_sig_docs]
Ancestors vfmTestDefs1416
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1416";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
