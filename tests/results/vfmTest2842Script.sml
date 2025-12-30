Theory vfmTest2842[no_sig_docs]
Ancestors vfmTestDefs2842
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2842";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
