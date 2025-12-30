Theory vfmTest0367[no_sig_docs]
Ancestors vfmTestDefs0367
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0367";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
