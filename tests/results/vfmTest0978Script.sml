Theory vfmTest0978[no_sig_docs]
Ancestors vfmTestDefs0978
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0978";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
