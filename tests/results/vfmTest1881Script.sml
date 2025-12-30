Theory vfmTest1881[no_sig_docs]
Ancestors vfmTestDefs1881
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1881";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
