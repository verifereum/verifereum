Theory vfmTest2022[no_sig_docs]
Ancestors vfmTestDefs2022
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2022";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
