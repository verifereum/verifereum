Theory vfmTest2805[no_sig_docs]
Ancestors vfmTestDefs2805
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2805";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
