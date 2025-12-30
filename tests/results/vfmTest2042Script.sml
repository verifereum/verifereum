Theory vfmTest2042[no_sig_docs]
Ancestors vfmTestDefs2042
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2042";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
