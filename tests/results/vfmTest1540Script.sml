Theory vfmTest1540[no_sig_docs]
Ancestors vfmTestDefs1540
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1540";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
