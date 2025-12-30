Theory vfmTest2704[no_sig_docs]
Ancestors vfmTestDefs2704
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2704";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
