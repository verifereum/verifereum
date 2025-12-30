Theory vfmTest2617[no_sig_docs]
Ancestors vfmTestDefs2617
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2617";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
