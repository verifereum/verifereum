Theory vfmTest2630[no_sig_docs]
Ancestors vfmTestDefs2630
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2630";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
