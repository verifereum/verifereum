Theory vfmTest0931[no_sig_docs]
Ancestors vfmTestDefs0931
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0931";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
