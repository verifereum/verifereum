Theory vfmTest2468[no_sig_docs]
Ancestors vfmTestDefs2468
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2468";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
