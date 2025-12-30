Theory vfmTest2046[no_sig_docs]
Ancestors vfmTestDefs2046
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2046";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
