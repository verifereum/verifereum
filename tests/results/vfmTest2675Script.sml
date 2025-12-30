Theory vfmTest2675[no_sig_docs]
Ancestors vfmTestDefs2675
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2675";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
