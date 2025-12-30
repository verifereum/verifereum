Theory vfmTest2446[no_sig_docs]
Ancestors vfmTestDefs2446
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2446";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
