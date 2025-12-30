Theory vfmTest1469[no_sig_docs]
Ancestors vfmTestDefs1469
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1469";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
