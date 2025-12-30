Theory vfmTest2151[no_sig_docs]
Ancestors vfmTestDefs2151
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2151";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
