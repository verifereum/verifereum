Theory vfmTest2033[no_sig_docs]
Ancestors vfmTestDefs2033
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2033";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
