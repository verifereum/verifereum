Theory vfmTest2062[no_sig_docs]
Ancestors vfmTestDefs2062
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2062";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
