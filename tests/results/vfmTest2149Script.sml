Theory vfmTest2149[no_sig_docs]
Ancestors vfmTestDefs2149
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2149";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
