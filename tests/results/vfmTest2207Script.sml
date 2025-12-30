Theory vfmTest2207[no_sig_docs]
Ancestors vfmTestDefs2207
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2207";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
