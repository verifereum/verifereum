Theory vfmTest0347[no_sig_docs]
Ancestors vfmTestDefs0347
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0347";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
