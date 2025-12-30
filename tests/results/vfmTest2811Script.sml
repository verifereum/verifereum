Theory vfmTest2811[no_sig_docs]
Ancestors vfmTestDefs2811
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2811";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
