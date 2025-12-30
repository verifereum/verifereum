Theory vfmTest2493[no_sig_docs]
Ancestors vfmTestDefs2493
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2493";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
