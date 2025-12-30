Theory vfmTest2400[no_sig_docs]
Ancestors vfmTestDefs2400
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2400";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
