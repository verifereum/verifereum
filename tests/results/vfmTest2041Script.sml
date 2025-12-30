Theory vfmTest2041[no_sig_docs]
Ancestors vfmTestDefs2041
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2041";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
