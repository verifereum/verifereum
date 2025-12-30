Theory vfmTest2765[no_sig_docs]
Ancestors vfmTestDefs2765
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2765";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
