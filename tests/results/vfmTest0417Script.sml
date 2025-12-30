Theory vfmTest0417[no_sig_docs]
Ancestors vfmTestDefs0417
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0417";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
