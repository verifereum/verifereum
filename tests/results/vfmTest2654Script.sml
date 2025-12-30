Theory vfmTest2654[no_sig_docs]
Ancestors vfmTestDefs2654
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2654";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
