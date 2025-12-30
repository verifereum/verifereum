Theory vfmTest2036[no_sig_docs]
Ancestors vfmTestDefs2036
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2036";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
