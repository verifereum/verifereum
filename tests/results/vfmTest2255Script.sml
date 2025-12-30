Theory vfmTest2255[no_sig_docs]
Ancestors vfmTestDefs2255
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2255";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
