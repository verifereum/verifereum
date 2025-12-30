Theory vfmTest1468[no_sig_docs]
Ancestors vfmTestDefs1468
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1468";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
