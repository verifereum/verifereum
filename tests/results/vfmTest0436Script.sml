Theory vfmTest0436[no_sig_docs]
Ancestors vfmTestDefs0436
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0436";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
