Theory vfmTest2758[no_sig_docs]
Ancestors vfmTestDefs2758
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2758";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
