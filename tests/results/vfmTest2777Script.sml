Theory vfmTest2777[no_sig_docs]
Ancestors vfmTestDefs2777
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2777";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
