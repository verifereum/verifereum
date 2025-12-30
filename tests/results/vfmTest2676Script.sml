Theory vfmTest2676[no_sig_docs]
Ancestors vfmTestDefs2676
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2676";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
