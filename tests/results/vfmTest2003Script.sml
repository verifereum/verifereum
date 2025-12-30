Theory vfmTest2003[no_sig_docs]
Ancestors vfmTestDefs2003
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2003";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
