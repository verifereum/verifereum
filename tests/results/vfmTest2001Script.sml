Theory vfmTest2001[no_sig_docs]
Ancestors vfmTestDefs2001
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2001";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
