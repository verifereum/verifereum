Theory vfmTest2742[no_sig_docs]
Ancestors vfmTestDefs2742
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2742";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
