Theory vfmTest2718[no_sig_docs]
Ancestors vfmTestDefs2718
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2718";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
