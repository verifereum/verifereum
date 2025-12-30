Theory vfmTest2176[no_sig_docs]
Ancestors vfmTestDefs2176
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2176";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
