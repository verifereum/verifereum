Theory vfmTest2354[no_sig_docs]
Ancestors vfmTestDefs2354
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2354";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
