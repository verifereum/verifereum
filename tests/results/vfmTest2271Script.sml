Theory vfmTest2271[no_sig_docs]
Ancestors vfmTestDefs2271
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2271";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
