Theory vfmTest2173[no_sig_docs]
Ancestors vfmTestDefs2173
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2173";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
