Theory vfmTest0325[no_sig_docs]
Ancestors vfmTestDefs0325
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0325";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
