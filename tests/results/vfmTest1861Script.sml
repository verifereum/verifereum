Theory vfmTest1861[no_sig_docs]
Ancestors vfmTestDefs1861
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1861";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
