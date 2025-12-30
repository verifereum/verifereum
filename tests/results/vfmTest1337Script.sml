Theory vfmTest1337[no_sig_docs]
Ancestors vfmTestDefs1337
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1337";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
