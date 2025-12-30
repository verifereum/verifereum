Theory vfmTest1338[no_sig_docs]
Ancestors vfmTestDefs1338
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1338";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
