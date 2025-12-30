Theory vfmTest2553[no_sig_docs]
Ancestors vfmTestDefs2553
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2553";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
