Theory vfmTest1604[no_sig_docs]
Ancestors vfmTestDefs1604
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1604";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
