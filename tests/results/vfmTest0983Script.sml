Theory vfmTest0983[no_sig_docs]
Ancestors vfmTestDefs0983
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0983";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
