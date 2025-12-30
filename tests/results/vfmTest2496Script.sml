Theory vfmTest2496[no_sig_docs]
Ancestors vfmTestDefs2496
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2496";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
