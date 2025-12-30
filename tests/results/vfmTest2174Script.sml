Theory vfmTest2174[no_sig_docs]
Ancestors vfmTestDefs2174
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2174";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
