Theory vfmTest2339[no_sig_docs]
Ancestors vfmTestDefs2339
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2339";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
