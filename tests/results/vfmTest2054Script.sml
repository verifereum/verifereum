Theory vfmTest2054[no_sig_docs]
Ancestors vfmTestDefs2054
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2054";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
