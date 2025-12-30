Theory vfmTest2645[no_sig_docs]
Ancestors vfmTestDefs2645
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2645";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
