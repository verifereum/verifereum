Theory vfmTest0770[no_sig_docs]
Ancestors vfmTestDefs0770
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0770";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
