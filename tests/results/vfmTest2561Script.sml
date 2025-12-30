Theory vfmTest2561[no_sig_docs]
Ancestors vfmTestDefs2561
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2561";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
