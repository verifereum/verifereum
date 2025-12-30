Theory vfmTest2846[no_sig_docs]
Ancestors vfmTestDefs2846
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2846";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
