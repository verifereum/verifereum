Theory vfmTest1893[no_sig_docs]
Ancestors vfmTestDefs1893
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1893";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
