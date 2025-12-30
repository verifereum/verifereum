Theory vfmTest0927[no_sig_docs]
Ancestors vfmTestDefs0927
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0927";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
