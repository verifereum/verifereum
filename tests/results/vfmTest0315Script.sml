Theory vfmTest0315[no_sig_docs]
Ancestors vfmTestDefs0315
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0315";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
