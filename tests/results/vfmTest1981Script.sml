Theory vfmTest1981[no_sig_docs]
Ancestors vfmTestDefs1981
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1981";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
