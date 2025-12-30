Theory vfmTest0035[no_sig_docs]
Ancestors vfmTestDefs0035
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0035";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
