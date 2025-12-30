Theory vfmTest2503[no_sig_docs]
Ancestors vfmTestDefs2503
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2503";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
