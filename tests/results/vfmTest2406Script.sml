Theory vfmTest2406[no_sig_docs]
Ancestors vfmTestDefs2406
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2406";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
