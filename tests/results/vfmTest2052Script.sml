Theory vfmTest2052[no_sig_docs]
Ancestors vfmTestDefs2052
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2052";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
