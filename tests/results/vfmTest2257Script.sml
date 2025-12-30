Theory vfmTest2257[no_sig_docs]
Ancestors vfmTestDefs2257
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2257";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
