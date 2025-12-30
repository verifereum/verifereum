Theory vfmTest2222[no_sig_docs]
Ancestors vfmTestDefs2222
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2222";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
