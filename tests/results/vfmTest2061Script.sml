Theory vfmTest2061[no_sig_docs]
Ancestors vfmTestDefs2061
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2061";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
