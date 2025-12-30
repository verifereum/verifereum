Theory vfmTest1245[no_sig_docs]
Ancestors vfmTestDefs1245
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1245";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
