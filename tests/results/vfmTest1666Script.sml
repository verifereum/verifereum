Theory vfmTest1666[no_sig_docs]
Ancestors vfmTestDefs1666
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1666";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
