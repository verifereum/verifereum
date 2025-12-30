Theory vfmTest2129[no_sig_docs]
Ancestors vfmTestDefs2129
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2129";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
