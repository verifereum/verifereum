Theory vfmTest0274[no_sig_docs]
Ancestors vfmTestDefs0274
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0274";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
