Theory vfmTest2687[no_sig_docs]
Ancestors vfmTestDefs2687
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2687";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
