Theory vfmTest2680[no_sig_docs]
Ancestors vfmTestDefs2680
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2680";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
