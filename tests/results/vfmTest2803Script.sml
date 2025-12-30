Theory vfmTest2803[no_sig_docs]
Ancestors vfmTestDefs2803
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs2803";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
