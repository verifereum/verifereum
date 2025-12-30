Theory vfmTest1963[no_sig_docs]
Ancestors vfmTestDefs1963
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1963";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
