Theory vfmTest0480[no_sig_docs]
Ancestors vfmTestDefs0480
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0480";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
