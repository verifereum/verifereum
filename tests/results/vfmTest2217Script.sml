Theory vfmTest2217[no_sig_docs]
Ancestors vfmTestDefs2217
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2217";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
