Theory vfmTest2782[no_sig_docs]
Ancestors vfmTestDefs2782
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2782";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
