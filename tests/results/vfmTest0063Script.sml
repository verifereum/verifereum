Theory vfmTest0063[no_sig_docs]
Ancestors vfmTestDefs0063
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0063";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
