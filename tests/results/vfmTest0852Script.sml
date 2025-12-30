Theory vfmTest0852[no_sig_docs]
Ancestors vfmTestDefs0852
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0852";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
