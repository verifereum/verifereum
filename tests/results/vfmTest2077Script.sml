Theory vfmTest2077[no_sig_docs]
Ancestors vfmTestDefs2077
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2077";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
