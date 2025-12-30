Theory vfmTest2014[no_sig_docs]
Ancestors vfmTestDefs2014
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2014";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
