Theory vfmTest1794[no_sig_docs]
Ancestors vfmTestDefs1794
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1794";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
