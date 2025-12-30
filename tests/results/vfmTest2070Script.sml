Theory vfmTest2070[no_sig_docs]
Ancestors vfmTestDefs2070
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2070";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
