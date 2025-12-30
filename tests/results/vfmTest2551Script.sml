Theory vfmTest2551[no_sig_docs]
Ancestors vfmTestDefs2551
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2551";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
