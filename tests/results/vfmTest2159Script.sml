Theory vfmTest2159[no_sig_docs]
Ancestors vfmTestDefs2159
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2159";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
