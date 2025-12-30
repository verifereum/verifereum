Theory vfmTest2662[no_sig_docs]
Ancestors vfmTestDefs2662
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2662";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
