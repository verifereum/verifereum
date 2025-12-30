Theory vfmTest2319[no_sig_docs]
Ancestors vfmTestDefs2319
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2319";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
