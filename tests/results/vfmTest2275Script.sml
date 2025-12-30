Theory vfmTest2275[no_sig_docs]
Ancestors vfmTestDefs2275
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2275";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
