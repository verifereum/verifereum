Theory vfmTest2075[no_sig_docs]
Ancestors vfmTestDefs2075
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2075";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
