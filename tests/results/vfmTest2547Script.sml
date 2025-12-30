Theory vfmTest2547[no_sig_docs]
Ancestors vfmTestDefs2547
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2547";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
