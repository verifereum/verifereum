Theory vfmTest2651[no_sig_docs]
Ancestors vfmTestDefs2651
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2651";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
