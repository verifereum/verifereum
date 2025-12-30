Theory vfmTest2114[no_sig_docs]
Ancestors vfmTestDefs2114
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2114";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
