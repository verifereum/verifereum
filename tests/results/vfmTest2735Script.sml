Theory vfmTest2735[no_sig_docs]
Ancestors vfmTestDefs2735
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2735";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
