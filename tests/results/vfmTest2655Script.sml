Theory vfmTest2655[no_sig_docs]
Ancestors vfmTestDefs2655
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2655";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
