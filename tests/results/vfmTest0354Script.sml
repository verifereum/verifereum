Theory vfmTest0354[no_sig_docs]
Ancestors vfmTestDefs0354
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0354";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
