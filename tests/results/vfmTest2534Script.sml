Theory vfmTest2534[no_sig_docs]
Ancestors vfmTestDefs2534
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2534";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
