Theory vfmTest2717[no_sig_docs]
Ancestors vfmTestDefs2717
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2717";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
