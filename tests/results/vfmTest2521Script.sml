Theory vfmTest2521[no_sig_docs]
Ancestors vfmTestDefs2521
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2521";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
