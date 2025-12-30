Theory vfmTest2533[no_sig_docs]
Ancestors vfmTestDefs2533
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2533";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
