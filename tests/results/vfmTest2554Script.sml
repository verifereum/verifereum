Theory vfmTest2554[no_sig_docs]
Ancestors vfmTestDefs2554
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2554";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
