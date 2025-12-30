Theory vfmTest2020[no_sig_docs]
Ancestors vfmTestDefs2020
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2020";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
