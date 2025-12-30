Theory vfmTest2478[no_sig_docs]
Ancestors vfmTestDefs2478
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2478";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
