Theory vfmTest2815[no_sig_docs]
Ancestors vfmTestDefs2815
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2815";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
