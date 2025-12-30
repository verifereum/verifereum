Theory vfmTest0544[no_sig_docs]
Ancestors vfmTestDefs0544
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0544";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
