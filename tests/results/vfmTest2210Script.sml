Theory vfmTest2210[no_sig_docs]
Ancestors vfmTestDefs2210
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2210";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
