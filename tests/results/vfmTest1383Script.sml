Theory vfmTest1383[no_sig_docs]
Ancestors vfmTestDefs1383
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1383";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
